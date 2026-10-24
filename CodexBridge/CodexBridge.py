# -*- coding: utf-8 -*-
"""CodexBridge 5 for IDLE: persistent editor integration and safe chat lifecycle.

Works with an existing authenticated Codex CLI. The plugin only gives Codex
read-only access; changes are applied by IDLE after explicit confirmation.
This module is loaded as an IDLE editor extension via config-extensions.def.
"""

from __future__ import annotations

import ast
from datetime import datetime
import difflib
import hashlib
import fnmatch
import os
from pathlib import Path
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import tkinter as tk
import time
import traceback
import uuid
from tkinter import messagebox, scrolledtext, simpledialog, ttk

PLUGIN_VERSION = "5.0.0 (2026-10-24)"
RUN_TIMEOUT_SECONDS = 30
MAX_RUNTIME_OUTPUT = 300_000
MAX_CODE_CHARS = 120_000
MAX_HISTORY_TURNS = 14
TIMEOUT_SECONDS = 360
BEGIN = "<<<BEGIN_PYTHON>>>"
END = "<<<END_PYTHON>>>"

CHAT_INSTRUCTION = (
    "Ты помощник-программист в IDLE. Отвечай на русском языке. "
    "В этом режиме объясняй код, предлагай решения, но не говори, что сам "
    "выполнил или изменил код. Весь код, если он приложен, находится в тексте запроса. "
    "Не пытайся редактировать файлы или исполнять программы."
)


def extract_fixed_source(answer):
    """Extract a delimited module without Markdown or other response text.

    The delimiter needs its own line; the newline just before END must be
    present for parsing and may be synthetic when the source lacks a final LF.
    """
    pattern = r"(?ms)^" + re.escape(BEGIN) + r"[ \t]*\r?\n(.*?)^" + re.escape(END) + r"[ \t]*(?:\r?\n|\Z)"
    found = list(re.finditer(pattern, answer))
    if len(found) != 1:
        raise ValueError("Codex должен вернуть ровно один полный Python-файл между маркерами.\n\n" + answer[-1600:])
    return found[0].group(1)


class CodexBridge:
    """IDLE extension entrypoint: IDLE instantiates CodexBridge(editwin)."""

    def __init__(self, editwin):
        self.editwin = editwin
        self.text = editwin.text
        self.dialog = None
        self.log_widget = None
        self.entry = None
        self.send_button = None
        self.include_code = None
        self.history = []
        self.messages = []   # (Tk text tag, author, content); reset on New chat
        self.popup_tag = None
        self.busy = False
        self.tasks = queue.Queue()
        self.polling = False
        self.after_id = None
        self.closed = False
        self.chat_generation = 0
        self.status_windows = set()
        self.file_browser = None
        self.navigator = None
        self.diagnostic_window = None
        self.last_diagnostic = None
        self.error_highlight = "codex_error_line"

        self.menu = tk.Menu(editwin.menubar, tearoff=False)
        self.menu.add_command(label="Исправить код в редакторе...", command=self.fix_code)
        self.menu.add_command(label="Проверить синтаксис (без запуска)", command=self.check_syntax)
        self.menu.add_command(label="▶ Запустить и проверить программу...", command=self.run_check)
        self.menu.add_command(label="Навигатор функций и классов...", command=self.show_navigator)
        self.menu.add_separator()
        self.menu.add_command(label="Чат с Codex...", command=self.open_chat)
        self.menu.add_command(label="Проводник дисков и файлов...", command=self.browse_files)
        self.menu.add_command(label="Объяснить код", command=lambda: self.quick("Объясни открытый код, назови возможные ошибки."))
        self.menu.add_command(label="Найти ошибки", command=lambda: self.quick("Найди ошибки и предложи конкретные исправления."))
        self.menu.add_separator()
        self.menu.add_command(label="Проверить подключение к редактору", command=self.diagnose)
        editwin.menubar.add_cascade(label="Codex", menu=self.menu)

    def browse_files(self):
        """Browse drives and directories without giving Codex disk access."""
        if self.closed:
            return
        browser = self.file_browser
        if browser is not None:
            try:
                if browser.top.winfo_exists():
                    browser.top.lift()
                    browser.top.focus_set()
                    return
            except tk.TclError:
                pass
        self.file_browser = CodexFileBrowser(self)

    def _filename(self):
        io = getattr(self.editwin, "io", None)
        return getattr(io, "filename", None) or "unsaved.py"

    def _buffer(self, selected_if_any=True):
        if selected_if_any:
            try:
                selected = self.text.get("sel.first", "sel.last")
                if selected.strip():
                    return selected, "выделенный фрагмент"
            except tk.TclError:
                pass
        return self.text.get("1.0", "end-1c"), "весь редактор"

    def diagnose(self):
        code, origin = self._buffer(False)
        messagebox.showinfo(
            "CodexBridge — IDLE",
            f"Версия: {PLUGIN_VERSION}\nОкно: {self.editwin.top.title()}\n"
            f"Файл: {self._filename()}\nИсточник: {origin}\n"
            f"Символов: {len(code)}\nCodex CLI: {self._cli_path() or 'не найден'}",
            parent=self.editwin.top,
        )

    def _cli_path(self):
        for exe in ("codex.cmd", "codex.exe", "codex"):
            match = shutil.which(exe)
            if match:
                return match
        path = Path(os.getenv("APPDATA", "")) / "npm" / "codex.cmd"
        return str(path) if path.is_file() else None

    def close(self):
        """Called by IDLE when the editor is closed; worker never owns Tk."""
        if self.closed:
            return
        self.closed = True
        self.chat_generation += 1
        self.polling = False
        if self.after_id is not None:
            try:
                self.editwin.top.after_cancel(self.after_id)
            except tk.TclError:
                pass
            self.after_id = None
        for window in tuple(self.status_windows):
            try:
                if window.winfo_exists():
                    window.destroy()
            except tk.TclError:
                pass
        self.status_windows.clear()
        if self.file_browser is not None:
            self.file_browser.close()
            self.file_browser = None
        if self.navigator is not None:
            self.navigator.close()
            self.navigator = None
        if self.diagnostic_window is not None:
            try:
                if self.diagnostic_window.winfo_exists():
                    self.diagnostic_window.destroy()
            except tk.TclError:
                pass
            self.diagnostic_window = None
        if self.dialog is not None:
            try:
                if self.dialog.winfo_exists():
                    self.dialog.destroy()
            except tk.TclError:
                pass
        self.dialog = None
        self.entry = None
        self.log_widget = None
        self.send_button = None
        self.history.clear()
        self.messages.clear()
        # Do not touch Tk again; an in-flight worker may still finish.

    def _poll_tasks(self):
        """GUI-only callback; stop scheduling when the work queue is empty."""
        self.after_id = None
        if self.closed:
            self.polling = False
            return
        while not self.closed:
            try:
                callback = self.tasks.get_nowait()
            except queue.Empty:
                break
            try:
                callback()
            except Exception as exc:
                if not self.closed:
                    try:
                        messagebox.showerror("CodexBridge", f"Ошибка интерфейса: {exc}", parent=self.editwin.top)
                    except tk.TclError:
                        pass
        if self.closed:
            self.polling = False
        elif self.busy or not self.tasks.empty():
            try:
                self.after_id = self.editwin.top.after(100, self._poll_tasks)
                self.polling = True
            except tk.TclError:
                self.polling = False
        else:
            self.polling = False

    def _start_polling(self):
        if self.closed:
            return
        if not self.polling:
            self.polling = True
            try:
                self.after_id = self.editwin.top.after(100, self._poll_tasks)
            except tk.TclError:
                self.polling = False

    @staticmethod
    def _call_codex(executable, prompt):
        """Use a private temp workspace and Codex's documented final-output file."""
        with tempfile.TemporaryDirectory(prefix="idle_codex_") as folder:
            final_file = Path(folder) / "last_response.txt"
            command = [
                executable, "exec", "--sandbox", "read-only",
                "--skip-git-repo-check", "--output-last-message", str(final_file), "-",
            ]
            completed = subprocess.run(
                command,
                input=prompt,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                encoding="utf-8",
                errors="replace",
                cwd=folder,
                timeout=TIMEOUT_SECONDS,
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )
            answer = final_file.read_text(encoding="utf-8-sig", errors="replace") if final_file.exists() else ""
            if completed.returncode != 0:
                error = (completed.stderr or completed.stdout or "Codex завершился с ошибкой").strip()
                raise RuntimeError(error[-3200:])
            if not answer.strip():
                raise RuntimeError("Codex завершил запрос без ответа.\n" + (completed.stderr or completed.stdout)[-1600:])
            return answer.strip()

    def _execute(self, prompt, done):
        """Launch one query at a time; worker never calls Tk."""
        if self.closed:
            return False
        if self.busy:
            messagebox.showinfo("Codex", "Предыдущий запрос ещё выполняется.", parent=self.editwin.top)
            return False
        exe = self._cli_path()
        if not exe:
            messagebox.showerror("Codex", "Не найден Codex CLI. Требуется установленный codex.cmd.", parent=self.editwin.top)
            return False
        self.busy = True
        self._start_polling()

        def work():
            try:
                result, error = self._call_codex(exe, prompt), None
            except Exception as exc:
                result, error = None, str(exc)
            self.tasks.put(lambda result=result, error=error: self._on_complete(done, result, error))

        threading.Thread(target=work, name="CodexBridge-worker", daemon=True).start()
        return True

    def _on_complete(self, done, result, error):
        self.busy = False
        if self.closed:
            return
        done(result, error)

    def _clipboard_copy(self, content):
        if not content:
            return
        top = self.editwin.top
        top.clipboard_clear()
        top.clipboard_append(content)
        top.update_idletasks()

    @staticmethod
    def _selected_text(widget):
        try:
            return widget.get("sel.first", "sel.last")
        except tk.TclError:
            return ""

    def _install_clipboard_menu(self, widget, readonly=False, chat_log=False):
        """Copy/Paste/Select All with no surprising implicit last-answer fallback."""
        menu = tk.Menu(widget, tearoff=False)
        menu.add_command(label="Копировать выделенное", command=lambda: self._clipboard_copy(self._selected_text(widget)))
        if chat_log:
            menu.add_command(label="Копировать сообщение под курсором", command=self.copy_popup_message)
            menu.add_command(label="Копировать последний ответ", command=self.copy_last_answer)
            menu.add_command(label="Копировать весь чат", command=self.copy_chat)
        if not readonly:
            menu.add_command(label="Вставить", command=lambda: self._paste(widget))
        menu.add_separator()
        menu.add_command(label="Выделить всё", command=lambda: self._select_all(widget))

        def popup(event):
            if chat_log:
                self.popup_tag = self._message_tag_at(widget.index(f"@{event.x},{event.y}"))
            menu.tk_popup(event.x_root, event.y_root)
            menu.grab_release()
            return "break"

        widget.bind("<Button-3>", popup, add="+")
        widget.bind("<Control-a>", lambda e: self._select_all(widget))
        widget.bind("<Control-c>", lambda e: (self._clipboard_copy(self._selected_text(widget)), "break")[1])
        if not readonly:
            widget.bind("<Control-v>", lambda e: (self._paste(widget), "break")[1])
        return menu

    @staticmethod
    def _select_all(widget):
        widget.tag_add("sel", "1.0", "end-1c")
        widget.focus_set()
        return "break"

    @staticmethod
    def _paste(widget):
        try:
            data = widget.clipboard_get()
            try:
                widget.delete("sel.first", "sel.last")
            except tk.TclError:
                pass
            widget.insert("insert", data)
        except tk.TclError:
            pass

    def _message_tag_at(self, index):
        if not self.log_widget:
            return None
        tags = self.log_widget.tag_names(index)
        return next((tag for tag in tags if tag.startswith("codex_msg_")), None)

    def copy_popup_message(self):
        for tag, _, content in self.messages:
            if tag == self.popup_tag:
                self._clipboard_copy(content)
                return

    def copy_last_answer(self):
        for _, author, content in reversed(self.messages):
            if author in ("Codex", "Ошибка"):
                self._clipboard_copy(content)
                return
        messagebox.showinfo("Codex", "Ответов в этом диалоге ещё нет.", parent=self.dialog)

    def copy_chat(self):
        if self.log_widget:
            self._clipboard_copy(self.log_widget.get("1.0", "end-1c"))

    def open_chat(self):
        if self.dialog is not None:
            try:
                if self.dialog.winfo_exists():
                    self.dialog.deiconify()
                    self.dialog.lift()
                    return
            except tk.TclError:
                pass
        if self.closed:
            return
        self.chat_generation += 1
        self.history = []
        self.messages = []
        self.popup_tag = None
        win = tk.Toplevel(self.editwin.top)
        self.dialog = win
        win.title("Codex Chat — Python IDLE")
        win.geometry("920x680")
        win.minsize(620, 430)

        log = scrolledtext.ScrolledText(win, wrap="word", state="disabled", exportselection=False)
        log.pack(fill="both", expand=True, padx=10, pady=(10, 4))
        self.log_widget = log
        self._install_clipboard_menu(log, readonly=True, chat_log=True)
        tools = tk.Frame(win)
        tools.pack(fill="x", padx=10, pady=3)
        tk.Button(tools, text="Копировать ответ", command=self.copy_last_answer).pack(side="left", padx=2)
        tk.Button(tools, text="Копировать выделенное", command=lambda: self._clipboard_copy(self._selected_text(log))).pack(side="left", padx=2)
        tk.Button(tools, text="Копировать весь чат", command=self.copy_chat).pack(side="left", padx=2)
        tk.Button(tools, text="Новый диалог", command=self.reset_chat).pack(side="right", padx=2)
        tk.Button(tools, text="Диски и файлы", command=self.browse_files).pack(side="right", padx=2)

        self.include_code = tk.BooleanVar(win, value=False)
        tk.Checkbutton(win, text="Приложить выделенный код (или весь файл) к следующему вопросу", variable=self.include_code).pack(anchor="w", padx=12, pady=(3, 0))
        bottom = tk.Frame(win)
        bottom.pack(fill="x", padx=10, pady=(5, 10))
        entry = tk.Text(bottom, height=4, wrap="word", exportselection=False)
        entry.pack(side="left", expand=True, fill="both")
        self._install_clipboard_menu(entry, readonly=False)
        self.entry = entry
        self.send_button = tk.Button(bottom, text="Отправить", command=self.send, width=14)
        self.send_button.pack(side="right", fill="y", padx=(8, 0))
        entry.bind("<Control-Return>", lambda e: (self.send(), "break")[1])
        self._append("Система", "Чат готов. Ctrl+Enter — отправить. Выделяй и копируй текст свободно.")
        entry.focus_set()

        def close():
            # Prevent a reply from an older closed window entering a new chat.
            self.chat_generation += 1
            self.dialog = None
            self.log_widget = None
            self.entry = None
            self.send_button = None
            self.include_code = None
            self.history = []
            self.messages = []
            win.destroy()

        win.protocol("WM_DELETE_WINDOW", close)

    def _append(self, author, content):
        log = self.log_widget
        if log is None:
            return
        try:
            if not log.winfo_exists():
                return
            log.configure(state="normal")
            start = log.index("end-1c")
            tag = f"codex_msg_{len(self.messages)}"
            log.insert("end", f"\n{author}:\n{content}\n")
            finish = log.index("end-1c")
            log.tag_add(tag, start, finish)
            if author in ("Codex", "Ошибка"):
                log.tag_config(tag, lmargin1=10, lmargin2=10)
            self.messages.append((tag, author, content))
            log.configure(state="disabled")
            log.see("end")
        except tk.TclError:
            pass

    def reset_chat(self):
        if self.busy:
            messagebox.showinfo("Codex", "Дождись окончания текущего запроса.", parent=self.dialog)
            return
        self.chat_generation += 1
        self.history = []
        self.messages = []
        self.popup_tag = None
        if self.log_widget:
            log = self.log_widget
            log.configure(state="normal")
            log.delete("1.0", "end")
            log.configure(state="disabled")
            self._append("Система", "Начат новый диалог.")

    def quick(self, instruction):
        self.open_chat()
        if self.entry is not None:
            self.entry.insert("end", instruction)
            self.include_code.set(True)
            self.send()

    def send(self):
        if self.dialog is None or self.entry is None or self.busy:
            return
        question = self.entry.get("1.0", "end-1c").strip()
        if not question:
            return
        code_section = ""
        if self.include_code.get():
            code, source = self._buffer()
            if code.strip():
                if len(code) > MAX_CODE_CHARS:
                    messagebox.showwarning("Codex", f"Код длиннее {MAX_CODE_CHARS} символов. Убери выделение или сократи файл.", parent=self.dialog)
                    return
                code_section = f"\n\nКод из IDLE ({self._filename()}, {source}):\n```python\n{code}\n```"
            self.include_code.set(False)
        content = question + code_section
        turns = (self.history + [("user", content)])[-MAX_HISTORY_TURNS:]
        history_prompt = "\n\n".join(f"<{author}>\n{msg}\n</{author}>" for author, msg in turns)
        prompt = CHAT_INSTRUCTION + "\n\nПереписка:\n" + history_prompt + "\n\nОтветь на последнее сообщение пользователя."
        self.entry.delete("1.0", "end")
        self._append("Ты", question + ("\n[Приложен код из IDLE]" if code_section else ""))
        self.send_button.configure(state="disabled")
        self._append("Система", "Codex обрабатывает запрос...")
        generation = self.chat_generation
        chat_window = self.dialog

        def complete(answer, error):
            if self.closed or generation != self.chat_generation or self.dialog is not chat_window:
                return
            if self.send_button is not None:
                self.send_button.configure(state="normal")
            if error:
                self._append("Ошибка", error)
            else:
                self.history.extend([("user", content), ("assistant", answer)])
                self.history = self.history[-MAX_HISTORY_TURNS:]
                self._append("Codex", answer)

        if not self._execute(prompt, complete):
            self.send_button.configure(state="normal")
            # Restore the draft when Codex couldn't start.
            self.entry.insert("1.0", question)

    def fix_code(self, traceback_text=None, auto_recheck=False):
        if self.busy:
            messagebox.showinfo("Codex", "Сначала дождись завершения запроса.", parent=self.editwin.top)
            return
        original, _ = self._buffer(False)
        if not original.strip():
            messagebox.showwarning("Codex", "В этом окне редактор пуст. Открой нужный .py-файл.", parent=self.editwin.top)
            return
        if len(original) > MAX_CODE_CHARS:
            messagebox.showwarning("Codex", "Файл слишком большой. Уменьши его или выбери часть для анализа в чате.", parent=self.editwin.top)
            return
        task = simpledialog.askstring(
            "Codex — исправление в IDLE", "Что необходимо исправить?",
            initialvalue=("Исправь ошибку из traceback, сохрани алгоритм и все математические формулы."
                          if traceback_text else "Исправь ошибки, сохрани смысл алгоритма и математические формулы."),
            parent=self.editwin.top,
        )
        if not task:
            return
        prompt = (
            "Исправь Python-файл, полностью приведённый ниже. Задание: " + task + "\n"
            + (("Диагностика Python (traceback/ошибка):\n" + traceback_text[-12000:] + "\n") if traceback_text else "") +
            "Верни только ПОЛНЫЙ исправленный исходник, строго между маркерами "
            f"{BEGIN} и {END}, каждый маркер на отдельной строке. "
            "Не вставляй Markdown, вступления, заключения и пояснения. "
            "Не читай файлы на диске, не запускай команды и не изменяй файлы. "
            "Не меняй математические формулы и логику, если они не связаны с указанной ошибкой. "
            "Если исправлять нечего, верни тот же текст без изменений.\n"
            f"Название: {Path(self._filename()).name}\n"
            "<<<ORIGINAL>>>\n" + original + "\n<<<END_ORIGINAL>>>"
        )
        status = tk.Toplevel(self.editwin.top)
        self.status_windows.add(status)
        status.title("Codex — анализ")
        status.transient(self.editwin.top)
        tk.Label(status, text="Codex готовит исправления. Твой исходный файл пока не изменяется.", padx=18, pady=22).pack()
        status.update_idletasks()

        def complete(answer, error):
            self.status_windows.discard(status)
            try:
                if status.winfo_exists():
                    status.destroy()
            except tk.TclError:
                pass
            if self.closed:
                return
            if error:
                messagebox.showerror("Codex", error, parent=self.editwin.top)
                return
            try:
                proposed = extract_fixed_source(answer)
                # A delimiter forces a newline before END; preserve source's
                # original final-newline convention where possible.
                if not original.endswith("\n") and proposed.endswith("\n"):
                    proposed = proposed[:-1]
                ast.parse(proposed, filename=self._filename())
            except (SyntaxError, ValueError) as exc:
                messagebox.showerror("Codex", f"Нельзя применить ответ:\n{exc}", parent=self.editwin.top)
                return
            if proposed == original:
                messagebox.showinfo("Codex", "Исправлений не требуется.", parent=self.editwin.top)
                return
            self._review_fix(original, proposed, after_apply=self.run_check if auto_recheck else None)

        if not self._execute(prompt, complete):
            self.status_windows.discard(status)
            status.destroy()

    def _review_fix(self, original, proposed, after_apply=None):
        if self.text.get("1.0", "end-1c") != original:
            messagebox.showwarning("Codex", "Текст в IDLE изменился во время запроса. Повтори анализ.", parent=self.editwin.top)
            return
        diff = list(difflib.unified_diff(
            original.splitlines(keepends=True), proposed.splitlines(keepends=True),
            fromfile="Оригинал IDLE", tofile="Предложение Codex", n=2,
        ))
        win = tk.Toplevel(self.editwin.top)
        self.status_windows.add(win)
        win.title("Codex — проверь изменения и примени в открытом IDLE")
        win.bind("<Destroy>", lambda event: self.status_windows.discard(win) if event.widget is win else None, add="+")
        win.geometry("940x640")
        tk.Label(win, text="Ни один файл на диске ещё не изменён. Внесение правок — только по кнопке ниже.", anchor="w", padx=12, pady=8).pack(fill="x")
        pane = scrolledtext.ScrolledText(win, state="normal", wrap="none", exportselection=False)
        pane.pack(fill="both", expand=True, padx=9, pady=5)
        pane.insert("1.0", "".join(diff)[:250000])
        pane.configure(state="disabled")
        self._install_clipboard_menu(pane, readonly=True)
        buttons = tk.Frame(win)
        buttons.pack(fill="x", padx=9, pady=9)
        tk.Button(buttons, text="Отмена", command=win.destroy).pack(side="right", padx=4)
        tk.Button(buttons, text="Применить в открытом редакторе IDLE", command=lambda: self._apply_fix(original, proposed, win, after_apply=after_apply)).pack(side="right", padx=4)

    def _apply_fix(self, original, proposed, preview, after_apply=None):
        if self.text.get("1.0", "end-1c") != original:
            messagebox.showwarning("Codex", "Редактор изменился. Исправления не применены.", parent=preview)
            return
        # Snapshot the actual IDLE buffer (even if it was never saved).
        # If backup fails, DO NOT modify the editor.
        try:
            backup_path = self._backup_buffer(original)
        except OSError as exc:
            messagebox.showerror("Codex", f"Резервная копия не создана; изменения отменены:\n{exc}", parent=preview)
            return
        old_lines = original.splitlines(keepends=True)
        new_lines = proposed.splitlines(keepends=True)
        changes = [item for item in difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False).get_opcodes() if item[0] != "equal"]
        undo = getattr(self.editwin, "undo", None)
        try:
            self.text.tag_delete("codex_changed")
        except tk.TclError:
            pass
        self.text.tag_configure("codex_changed", background="#DFF5DC")
        # Use IDLE's UndoDelegator when present, avoiding separate undo steps.
        if undo is not None and hasattr(undo, "undo_block_start"):
            undo.undo_block_start()
        else:
            self.text.edit_separator()
        try:
            self.text.delete("1.0", "end-1c")
            self.text.insert("1.0", proposed)
        finally:
            if undo is not None and hasattr(undo, "undo_block_stop"):
                undo.undo_block_stop()
            else:
                self.text.edit_separator()
        first = None
        for _, i1, i2, j1, j2 in changes:
            if first is None:
                first = j1 + 1
            if j2 > j1:
                self.text.tag_add("codex_changed", f"{j1 + 1}.0", f"{j2 + 1}.0")
            elif new_lines:
                line = min(j1 + 1, len(new_lines))
                self.text.tag_add("codex_changed", f"{line}.0", f"{line}.end")
        if first is not None:
            self.text.mark_set("insert", f"{min(first, max(len(new_lines), 1))}.0")
            self.text.see("insert")
        self.text.focus_set()
        preview.destroy()
        messagebox.showinfo(
            "Codex — готово",
            "Исправления внесены непосредственно в открытый редактор IDLE.\n"
            "Изменённые строки подсвечены.\n"
            "Ctrl+Z — отменить; Ctrl+S — сохранить на диск.\n"
            f"Резервная копия: {backup_path}",
            parent=self.editwin.top,
        )
        if after_apply is not None and not self.closed:
            after_apply()


    def _backup_buffer(self, text):
        """Crash-safe snapshot before replacing buffer. No changes to project files."""
        folder = Path.home() / "IDLE_Codex_Backups" / "snapshots"
        folder.mkdir(parents=True, exist_ok=True)
        stem = re.sub(r"[^a-zA-Z0-9_.-]+", "_", Path(self._filename()).stem)[:45] or "untitled"
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
        filename = folder / f"{stem}_{stamp}_{uuid.uuid4().hex[:8]}.py"
        # 'x' avoids silently overwriting an earlier snapshot.
        with filename.open("x", encoding="utf-8", newline="") as out:
            out.write(text)
            out.flush()
            os.fsync(out.fileno())
        return filename

    def _reset_error_mark(self):
        try:
            self.text.tag_remove(self.error_highlight, "1.0", "end")
        except tk.TclError:
            pass

    def _highlight_error(self, line):
        """Marks the actual editable Tk buffer, never the disk file."""
        self._reset_error_mark()
        line = max(1, int(line))
        self.text.tag_configure(self.error_highlight, background="#FFE8BB")
        self.text.tag_add(self.error_highlight, f"{line}.0", f"{line}.end+1c")
        self.text.tag_raise(self.error_highlight)
        self.text.mark_set("insert", f"{line}.0")
        self.text.see(f"{line}.0")
        self.text.focus_set()

    @staticmethod
    def _parse_traceback_line(output, filename):
        """Find latest frame referring to original filename, not imported modules."""
        rx = re.compile(r'(?m)^\s*File ["\'](.+?)["\'], line (\d+)')
        target = os.path.normcase(os.path.abspath(filename))
        matches = []
        for m in rx.finditer(output):
            loc = os.path.normcase(os.path.abspath(m.group(1)))
            if loc == target:
                matches.append(int(m.group(2)))
        return matches[-1] if matches else None

    def _effective_filename(self):
        filename = self._filename()
        if filename == "unsaved.py":
            return str(Path.home() / "unsaved_IDLEx.py")
        return str(Path(filename).resolve())

    def show_navigator(self):
        if self.closed:
            return
        if self.navigator is not None:
            try:
                if self.navigator.top.winfo_exists():
                    self.navigator.top.lift()
                    self.navigator.refresh()
                    return
            except tk.TclError:
                pass
        self.navigator = CodexSymbolNavigator(self)

    def check_syntax(self):
        if self.closed:
            return
        source, _ = self._buffer(False)
        try:
            ast.parse(source, filename=self._effective_filename())
        except SyntaxError as exc:
            desc = "".join(traceback.format_exception_only(type(exc), exc))
            self._show_diagnostic(False, desc, exc.lineno or 1)
        else:
            self._reset_error_mark()
            messagebox.showinfo("Codex — синтаксис", "Синтаксис корректен.\nЭто НЕ проверка исполнения программы.", parent=self.editwin.top)

    @staticmethod
    def _execute_python_buffer(source, filename):
        """Explicit user-triggered execution (NOT a security sandbox).

        Runs exactly the visible unsaved code, with filename and sys.path set
        to the opened project's path. Stdout and stderr go to a temporary
        file, bounded by a monitor. The original .py is never overwritten.
        """
        project_dir = Path(filename).parent
        if not project_dir.exists():
            project_dir = Path.home()
        # IDLE on Windows is usually hosted by pythonw.exe, which has no console.
        executable = Path(sys.executable)
        if executable.name.lower() == "pythonw.exe" and executable.with_name("python.exe").is_file():
            executable = executable.with_name("python.exe")
        script = (
            "import sys, pathlib\n"
            "_file = sys.argv[1]\n"
            "_source = sys.stdin.buffer.read().decode('utf-8')\n"
            "sys.argv = [_file]\n"
            "sys.path.insert(0, str(pathlib.Path(_file).resolve().parent))\n"
            "_namespace = {'__name__':'__main__','__file__':_file,'__package__':None,'__cached__':None}\n"
            "exec(compile(_source, _file, 'exec'), _namespace)\n"
        )
        command = [str(executable), "-X", "utf8", "-B", "-u", "-c", script, filename]
        deadline = time.monotonic() + RUN_TIMEOUT_SECONDS
        with tempfile.TemporaryFile(mode="w+b") as output:
            process = subprocess.Popen(
                command, cwd=str(project_dir), stdin=subprocess.PIPE,
                stdout=output, stderr=subprocess.STDOUT,
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )
            timed_out, overflow = False, False
            try:
                process.stdin.write(source.encode("utf-8"))
                process.stdin.close()
                while process.poll() is None:
                    if time.monotonic() > deadline:
                        timed_out = True
                        process.kill()
                        break
                    if os.fstat(output.fileno()).st_size > MAX_RUNTIME_OUTPUT:
                        overflow = True
                        process.kill()
                        break
                    time.sleep(0.08)
                process.wait(timeout=4)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()
            output.seek(0)
            data = output.read(MAX_RUNTIME_OUTPUT + 1)
        output_text = data.decode("utf-8", errors="replace")
        if timed_out:
            output_text += f"\n[CodexBridge: выполнение остановлено после {RUN_TIMEOUT_SECONDS} секунд]"
        if overflow or len(data) > MAX_RUNTIME_OUTPUT:
            output_text = output_text[:MAX_RUNTIME_OUTPUT] + "\n[CodexBridge: вывод ограничен]"
        return {"returncode": process.returncode, "output": output_text,
                "timeout": timed_out, "overflow": overflow}

    def run_check(self):
        """Syntax-check, then optionally run current (possibly unsaved) editor code."""
        if self.closed or self.busy:
            if not self.closed:
                messagebox.showinfo("Codex", "Предыдущая операция ещё выполняется.", parent=self.editwin.top)
            return
        source, _ = self._buffer(False)
        if not source.strip():
            messagebox.showwarning("Codex", "Редактор пуст.", parent=self.editwin.top)
            return
        if len(source) > MAX_CODE_CHARS:
            messagebox.showwarning("Codex", "Исходник превышает ограничение на размер.", parent=self.editwin.top)
            return
        filename = self._effective_filename()
        try:
            ast.parse(source, filename=filename)
        except SyntaxError as exc:
            desc = "".join(traceback.format_exception_only(type(exc), exc))
            self._show_diagnostic(False, desc, exc.lineno or 1)
            return
        if not messagebox.askyesno(
            "Codex — запуск Python",
            "Запустить код из открытого буфера IDLE?\n\n"
            "Это РЕАЛЬНОЕ выполнение Python в Windows с твоими правами.\n"
            "Программа может изменять файлы, запускать процессы и обращаться к сети.\n"
            f"Рабочая папка: {Path(filename).parent}\n"
            f"Ограничение: {RUN_TIMEOUT_SECONDS} секунд.\n"
            "Отмена безопасно пропустит запуск.",
            parent=self.editwin.top,
        ):
            return
        self._reset_error_mark()
        status = tk.Toplevel(self.editwin.top)
        self.status_windows.add(status)
        status.title("Codex — запуск Python")
        tk.Label(status, text="Python проверяет текущий буфер...", padx=18, pady=20).pack()
        self.busy = True
        self._start_polling()

        def work():
            try:
                result, error = self._execute_python_buffer(source, filename), None
            except Exception as exc:
                result, error = None, f"{type(exc).__name__}: {exc}"
            self.tasks.put(lambda result=result, error=error: self._on_complete(finished, result, error))

        def finished(result, error):
            self.status_windows.discard(status)
            try:
                if status.winfo_exists():
                    status.destroy()
            except tk.TclError:
                pass
            if self.closed:
                return
            if self.text.get("1.0", "end-1c") != source:
                messagebox.showwarning("Codex", "Пока программа выполнялась, текст изменился. Результат относится к старой версии буфера.", parent=self.editwin.top)
                return
            if error:
                self._show_diagnostic(False, "Ошибка запуска Python: " + error, None)
                return
            self.last_diagnostic = result
            good = result["returncode"] == 0 and not result["timeout"] and not result["overflow"]
            line = self._parse_traceback_line(result["output"], filename) if not good else None
            diagnostic = (
                f"Код завершения: {result['returncode']}\n"
                f"Файл: {filename}\n"
                f"--------------------------------\n"
                + (result["output"] or "[Программа не вывела текста]")
            )
            self._show_diagnostic(good, diagnostic, line)

        threading.Thread(target=work, name="CodexBridge-python-check", daemon=True).start()

    @staticmethod
    def _diagnostic_hint(details):
        """Conservative, local explanation before asking Codex for a precise fix."""
        hints = (
            ("ZeroDivisionError", "Деление на ноль. Проверь знаменатель и ветвление перед делением."),
            ("NameError", "Имя не определено. Проверь написание, область видимости и инициализацию переменной."),
            ("ModuleNotFoundError", "Модуль не найден. Проверь окружение Python и установку зависимости."),
            ("IndexError", "Индекс вне границ последовательности. Проверь диапазон индекса."),
            ("KeyError", "Ключ отсутствует в словаре. Проверь наличие ключа до обращения."),
            ("AttributeError", "Атрибут отсутствует у объекта. Проверь тип объекта и имя атрибута."),
            ("TypeError", "Несовместимые типы или неверные аргументы. Проверь используемую операцию."),
            ("SyntaxError", "Синтаксис Python нарушен. Проверь указанную строку и соседние строки."),
            ("IndentationError", "Неверный отступ. Проверь выравнивание блоков Python."),
        )
        return next((hint for error, hint in hints if error in details),
                    "Причину уточнит traceback; Codex предложит исправление только по твоему запросу.")

    def _show_diagnostic(self, success, details, line=None):
        if self.closed:
            return
        if line is not None:
            self._highlight_error(line)
        else:
            self._reset_error_mark()
        if self.diagnostic_window is not None:
            try:
                if self.diagnostic_window.winfo_exists():
                    self.diagnostic_window.destroy()
            except tk.TclError:
                pass
        win = tk.Toplevel(self.editwin.top)
        self.diagnostic_window = win
        win.title("Codex — проверка успешна" if success else "Codex — ошибка Python")
        # Place to the right of the IDLE window when there is room.
        self.editwin.top.update_idletasks()
        x = self.editwin.top.winfo_rootx() + min(self.editwin.top.winfo_width() - 30, 600)
        y = self.editwin.top.winfo_rooty() + 60
        win.geometry(f"620x420+{max(0, x)}+{max(0, y)}")
        heading = ("✓ Python завершился успешно." if success else
                   f"Ошибка в строке {line}" if line is not None else "Ошибка выполнения (строка не определена)")
        tk.Label(win, text=heading, anchor="w", padx=10, pady=8).pack(fill="x")
        if not success:
            tk.Label(win, text=self._diagnostic_hint(details), anchor="w",
                     justify="left", wraplength=570, padx=10, pady=4).pack(fill="x")
        editor = scrolledtext.ScrolledText(win, wrap="word", state="normal", exportselection=False)
        editor.pack(fill="both", expand=True, padx=8)
        editor.insert("1.0", details)
        editor.configure(state="disabled")
        self._install_clipboard_menu(editor, readonly=True)
        row = tk.Frame(win)
        row.pack(fill="x", padx=8, pady=8)
        tk.Button(row, text="Копировать вывод", command=lambda: self._clipboard_copy(details)).pack(side="left", padx=3)
        if not success:
            tk.Button(row, text="Исправить с Codex...", command=lambda: self.fix_code(traceback_text=details, auto_recheck=True)).pack(side="left", padx=3)
        tk.Button(row, text="Закрыть", command=win.destroy).pack(side="right", padx=3)
        def closed(event=None):
            if event is not None and event.widget is not win:
                return
            if self.diagnostic_window is win:
                self.diagnostic_window = None
        win.bind("<Destroy>", closed, add="+")


class CodexSymbolNavigator:
    """AST-backed symbol tree for open IDLE buffer; never scans user drives."""
    def __init__(self, bridge):
        self.bridge = bridge
        self.top = tk.Toplevel(bridge.editwin.top)
        self.top.title("Codex — функции и классы")
        self.top.geometry("470x620")
        self.entries = {}
        topbar = tk.Frame(self.top)
        topbar.pack(fill="x", padx=7, pady=6)
        tk.Button(topbar, text="Обновить (F5)", command=self.refresh).pack(side="left")
        tk.Button(topbar, text="К текущей строке", command=self.current_line).pack(side="left", padx=4)
        self.status = tk.StringVar(self.top, "")
        tk.Label(self.top, textvariable=self.status, anchor="w").pack(fill="x", padx=8)
        outer = tk.Frame(self.top)
        outer.pack(fill="both", expand=True, padx=7, pady=7)
        self.tree = ttk.Treeview(outer, columns=("line",), show="tree headings")
        self.tree.heading("#0", text="Символ")
        self.tree.heading("line", text="Строка")
        self.tree.column("#0", width=335, stretch=True)
        self.tree.column("line", width=65, anchor="e", stretch=False)
        sb = ttk.Scrollbar(outer, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<Double-Button-1>", self.go_to_symbol)
        self.tree.bind("<Return>", self.go_to_symbol)
        self.top.bind("<F5>", lambda event: self.refresh())
        self.top.protocol("WM_DELETE_WINDOW", self.close)
        self.refresh()

    def refresh(self):
        code = self.bridge.text.get("1.0", "end-1c")
        self.tree.delete(*self.tree.get_children())
        self.entries.clear()
        try:
            root = ast.parse(code, filename=self.bridge._filename())
        except SyntaxError as exc:
            self.status.set(f"Синтаксическая ошибка, строка {exc.lineno}: {exc.msg}")
            return
        count = 0
        def walk(body, parent=""):
            nonlocal count
            for node in body:
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    is_class = isinstance(node, ast.ClassDef)
                    mark = "◆ " if is_class else ("async ƒ " if isinstance(node, ast.AsyncFunctionDef) else "ƒ ")
                    item = self.tree.insert(parent, "end", text=mark + node.name,
                                            values=(node.lineno,), open=True)
                    self.entries[item] = node.lineno
                    count += 1
                    walk(node.body, item)
        walk(root.body)
        self.status.set(f"{self.bridge._filename()} — {count} символов. Двойной щелчок: перейти к строке.")

    def go_to_symbol(self, event=None):
        selected = self.tree.selection()
        if not selected:
            return
        line = self.entries.get(selected[0])
        if not line:
            return
        text = self.bridge.text
        text.tag_remove("codex_symbol_line", "1.0", "end")
        text.tag_configure("codex_symbol_line", background="#E3F0FF")
        text.tag_add("codex_symbol_line", f"{line}.0", f"{line}.end+1c")
        text.mark_set("insert", f"{line}.0")
        text.see(f"{line}.0")
        text.focus_set()

    def current_line(self):
        line = int(self.bridge.text.index("insert").split(".")[0])
        nearest = min(self.entries, key=lambda key: abs(self.entries[key] - line)) if self.entries else None
        if nearest is not None:
            self.tree.selection_set(nearest)
            self.tree.see(nearest)

    def close(self):
        if self.bridge.navigator is self:
            self.bridge.navigator = None
        try:
            self.top.destroy()
        except tk.TclError:
            pass



class CodexFileBrowser:
    """Two browsing layouts: separate folder/file panes or one expandable tree.

    File access is local and on-demand. Nothing in this browser is sent to Codex.
    A chosen file can be opened in the linked IDLE editor through its FileList.
    """

    MAX_ENTRIES = 2500

    def __init__(self, bridge):
        self.bridge = bridge
        self.top = tk.Toplevel(bridge.editwin.top)
        self.top.title("Codex — диски и файлы")
        self.top.geometry("1000x660")
        self.top.minsize(720, 430)
        self.top.protocol("WM_DELETE_WINDOW", self.close)
        self.mode = tk.StringVar(self.top, "separate")
        self.path_var = tk.StringVar(self.top)
        self.filter_var = tk.StringVar(self.top, "*")
        self.status_var = tk.StringVar(self.top, "")
        self.current_dir = None
        self.folder_paths = {}
        self.all_paths = {}
        self.file_paths = {}
        self.folder_loaded = set()
        self.all_loaded = set()
        self._counter = 0
        self._busy_navigation = False

        toolbar = ttk.Frame(self.top, padding=(9, 9, 9, 5))
        toolbar.pack(fill="x")
        ttk.Label(toolbar, text="Адрес:").pack(side="left", padx=(0, 5))
        self.path_entry = ttk.Entry(toolbar, textvariable=self.path_var)
        self.path_entry.pack(side="left", fill="x", expand=True, padx=(0, 6))
        self.path_entry.bind("<Return>", lambda event: self.go_to_address())
        ttk.Button(toolbar, text="Перейти", command=self.go_to_address).pack(side="left", padx=2)
        ttk.Button(toolbar, text="↑", width=3, command=self.up).pack(side="left", padx=2)
        ttk.Button(toolbar, text="Обновить", command=self.refresh).pack(side="left", padx=2)

        modebar = ttk.Frame(self.top, padding=(10, 3, 10, 7))
        modebar.pack(fill="x")
        ttk.Label(modebar, text="Показывать:").pack(side="left")
        ttk.Radiobutton(modebar, text="Раздельно: папки / файлы", value="separate", variable=self.mode,
                        command=self.show_mode).pack(side="left", padx=(9, 10))
        ttk.Radiobutton(modebar, text="Вместе: диски + папки + файлы", value="combined", variable=self.mode,
                        command=self.show_mode).pack(side="left")
        ttk.Label(modebar, text="Фильтр файлов:").pack(side="left", padx=(25, 5))
        filter_entry = ttk.Entry(modebar, width=15, textvariable=self.filter_var)
        filter_entry.pack(side="left")
        filter_entry.bind("<Return>", lambda event: self.refresh())
        ttk.Button(modebar, text="Применить", command=self.refresh).pack(side="left", padx=3)

        self.body = ttk.Frame(self.top, padding=(9, 0, 9, 4))
        self.body.pack(fill="both", expand=True)
        self.separate = ttk.Panedwindow(self.body, orient="horizontal")
        self.folder_holder = ttk.Frame(self.separate)
        self.file_holder = ttk.Frame(self.separate)
        self.folders = ttk.Treeview(self.folder_holder, show="tree", selectmode="browse")
        self.files = ttk.Treeview(self.file_holder, columns=("type", "size"), show="tree headings", selectmode="browse")
        self.files.heading("#0", text="Имя файла / папки")
        self.files.heading("type", text="Тип")
        self.files.heading("size", text="Размер")
        self.files.column("#0", width=380)
        self.files.column("type", width=95, anchor="w", stretch=False)
        self.files.column("size", width=115, anchor="e", stretch=False)
        self._scrollable(self.separate, self.folder_holder, self.folders, 310)
        self._scrollable(self.separate, self.file_holder, self.files, 630)
        self.folders.bind("<<TreeviewOpen>>", self._expand_folder)
        self.folders.bind("<<TreeviewSelect>>", self._selected_folder)
        self.files.bind("<Double-1>", self._double_file)
        self.files.bind("<Return>", lambda event: self.open_selected())

        self.combined = ttk.Frame(self.body)
        self.alltree = ttk.Treeview(self.combined, columns=("type", "size"), show="tree headings", selectmode="browse")
        self.alltree.heading("#0", text="Диск / папка / файл")
        self.alltree.heading("type", text="Тип")
        self.alltree.heading("size", text="Размер")
        self.alltree.column("#0", width=650)
        self.alltree.column("type", width=95, anchor="w", stretch=False)
        self.alltree.column("size", width=110, anchor="e", stretch=False)
        self.alltree.pack(side="left", fill="both", expand=True)
        combined_scroll = ttk.Scrollbar(self.combined, orient="vertical", command=self.alltree.yview)
        combined_scroll.pack(side="right", fill="y")
        self.alltree.configure(yscrollcommand=combined_scroll.set)
        self.alltree.bind("<<TreeviewOpen>>", self._expand_all)
        self.alltree.bind("<<TreeviewSelect>>", self._selected_all)
        self.alltree.bind("<Double-1>", self._double_all)
        self.alltree.bind("<Return>", lambda event: self.open_selected())

        controls = ttk.Frame(self.top, padding=(9, 7, 9, 3))
        controls.pack(fill="x")
        ttk.Button(controls, text="Открыть файл в IDLE", command=self.open_selected).pack(side="left", padx=3)
        ttk.Button(controls, text="Копировать путь", command=self.copy_path).pack(side="left", padx=3)
        ttk.Button(controls, text="Открыть в Проводнике Windows", command=self.open_in_windows).pack(side="left", padx=3)
        ttk.Button(controls, text="Закрыть", command=self.close).pack(side="right", padx=3)
        ttk.Label(self.top, textvariable=self.status_var, anchor="w", padding=(12, 3)).pack(fill="x")

        start = Path(bridge._filename())
        if start.name == "unsaved.py" or not start.exists():
            start = Path.home()
        elif start.is_file():
            start = start.parent
        self._load_roots()
        self.show_mode()
        self.navigate(start)

    @staticmethod
    def _scrollable(paned, holder, tree, width):
        bar = ttk.Scrollbar(holder, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=bar.set)
        tree.pack(side="left", fill="both", expand=True)
        bar.pack(side="right", fill="y")
        paned.add(holder, weight=max(width // 100, 1))

    @staticmethod
    def _drives():
        if os.name == "nt":
            try:
                import ctypes
                mask = ctypes.windll.kernel32.GetLogicalDrives()
                drives = [Path(chr(65 + i) + ":" + chr(92)) for i in range(26) if mask & (1 << i)]
                if drives:
                    return drives
            except (AttributeError, OSError):
                pass
            return [Path(letter + ":" + chr(92)) for letter in "CDEFGHIJKLMNOPQRSTUVWXYZ" if Path(letter + ":" + chr(92)).exists()]
        return [Path("/"), Path.home()]

    def _nextid(self):
        self._counter += 1
        return f"codex_file_{self._counter}"

    def _load_roots(self):
        self.folders.delete(*self.folders.get_children(""))
        self.alltree.delete(*self.alltree.get_children(""))
        self.folder_paths.clear()
        self.all_paths.clear()
        self.folder_loaded.clear()
        self.all_loaded.clear()
        for root in dict.fromkeys(self._drives()):
            label = str(root)
            i = self._nextid()
            self.folders.insert("", "end", iid=i, text=label)
            self.folder_paths[i] = root
            self.folders.insert(i, "end", iid=self._nextid(), text="...")
            j = self._nextid()
            self.alltree.insert("", "end", iid=j, text=label, values=("Диск", ""))
            self.all_paths[j] = root
            self.alltree.insert(j, "end", iid=self._nextid(), text="...")

    def _entries(self, folder, only_dirs=False):
        items = []
        total_more = False
        try:
            with os.scandir(folder) as scanned:
                for entry in scanned:
                    try:
                        is_dir = entry.is_dir(follow_symlinks=True)
                        if only_dirs and not is_dir:
                            continue
                        if not is_dir and not fnmatch.fnmatch(entry.name.lower(), (self.filter_var.get().strip() or "*").lower()):
                            continue
                        items.append((entry.name, is_dir, Path(entry.path)))
                        if len(items) > self.MAX_ENTRIES:
                            total_more = True
                            break
                    except OSError:
                        continue
        except OSError as exc:
            return [], False, str(exc)
        items.sort(key=lambda x: (not x[1], x[0].casefold()))
        return items[:self.MAX_ENTRIES], total_more, ""

    def _size_label(self, path):
        try:
            size = path.stat().st_size
        except OSError:
            return ""
        for unit in ("Б", "КБ", "МБ", "ГБ"):
            if size < 1024 or unit == "ГБ":
                return f"{size:.1f} {unit}" if unit != "Б" else f"{size} Б"
            size /= 1024
        return ""

    def _populate(self, tree, paths, loaded, item, only_dirs):
        if item in loaded or item not in paths:
            return
        loaded.add(item)
        for child in tree.get_children(item):
            tree.delete(child)
        folder = paths[item]
        entries, truncated, error = self._entries(folder, only_dirs=only_dirs)
        if error:
            self.status_var.set(f"Нет доступа к {folder}: {error}")
        for name, is_dir, path in entries:
            i = self._nextid()
            tree.insert(item, "end", iid=i, text=name,
                        values=() if only_dirs else ("Папка" if is_dir else "Файл", "" if is_dir else self._size_label(path)))
            paths[i] = path
            if is_dir:
                tree.insert(i, "end", iid=self._nextid(), text="...")
        if truncated:
            self.status_var.set(f"{folder}: показаны первые {self.MAX_ENTRIES} элементов. Используй точный путь в поле «Адрес».")

    def _expand_folder(self, event=None):
        item = self.folders.focus()
        if item:
            self._populate(self.folders, self.folder_paths, self.folder_loaded, item, True)

    def _expand_all(self, event=None):
        item = self.alltree.focus()
        if item:
            self._populate(self.alltree, self.all_paths, self.all_loaded, item, False)

    def _selected_folder(self, event=None):
        if self._busy_navigation:
            return
        selected = self.folders.selection()
        if selected and selected[0] in self.folder_paths:
            path = self.folder_paths[selected[0]]
            if path != self.current_dir:
                self.navigate(path, synchronize=False)

    def _selected_all(self, event=None):
        selected = self.alltree.selection()
        if selected and selected[0] in self.all_paths:
            path = self.all_paths[selected[0]]
            if path.is_dir() and path != self.current_dir:
                self.navigate(path, synchronize=False)

    def _ensure_selection(self, tree, paths, loaded, directory, only_dirs):
        # Expand one branch to the current directory; never scan a whole drive.
        normalized = directory.resolve(strict=False)
        anchor = Path(normalized.anchor or "/")
        roots = {path: item for item, path in paths.items() if tree.parent(item) == ""}
        root_id = roots.get(anchor)
        if root_id is None:
            root_id = self._nextid()
            tree.insert("", "end", iid=root_id, text=str(anchor), values=() if only_dirs else ("Диск", ""))
            paths[root_id] = anchor
            tree.insert(root_id, "end", iid=self._nextid(), text="...")
        curr_id = root_id
        curr_path = anchor
        chunks = normalized.parts[1:]
        for chunk in chunks:
            self._populate(tree, paths, loaded, curr_id, only_dirs)
            next_path = curr_path / chunk
            child_id = next((c for c in tree.get_children(curr_id) if paths.get(c) == next_path), None)
            if child_id is None:
                child_id = self._nextid()
                tree.insert(curr_id, "end", iid=child_id, text=chunk, values=() if only_dirs else ("Папка", ""))
                paths[child_id] = next_path
                tree.insert(child_id, "end", iid=self._nextid(), text="...")
            tree.item(curr_id, open=True)
            curr_id, curr_path = child_id, next_path
        self._busy_navigation = True
        try:
            tree.selection_set(curr_id)
            tree.focus(curr_id)
            tree.see(curr_id)
        finally:
            self._busy_navigation = False

    def navigate(self, target, synchronize=True):
        try:
            target = Path(target).expanduser().resolve(strict=False)
            if target.is_file():
                target = target.parent
            if not target.is_dir():
                raise NotADirectoryError(f"Папка не найдена: {target}")
        except (OSError, ValueError) as exc:
            messagebox.showerror("Codex — проводник", str(exc), parent=self.top)
            return
        self.current_dir = target
        self.path_var.set(str(target))
        self._render_files()
        if synchronize:
            if self.mode.get() == "combined":
                self._ensure_selection(self.alltree, self.all_paths, self.all_loaded, target, False)
            else:
                self._ensure_selection(self.folders, self.folder_paths, self.folder_loaded, target, True)

    def _render_files(self):
        self.files.delete(*self.files.get_children(""))
        self.file_paths.clear()
        items, truncated, error = self._entries(self.current_dir)
        if error:
            self.status_var.set(f"Нет доступа: {error}")
            return
        for name, is_dir, path in items:
            i = self._nextid()
            self.files.insert("", "end", iid=i, text=name, values=("Папка" if is_dir else "Файл", "" if is_dir else self._size_label(path)))
            self.file_paths[i] = path
        msg = f"{self.current_dir} — показано {len(items)} элементов"
        if truncated:
            msg += f" (ограничено {self.MAX_ENTRIES}; можно ввести путь вручную)"
        self.status_var.set(msg)

    def show_mode(self):
        self.separate.pack_forget()
        self.combined.pack_forget()
        if self.mode.get() == "combined":
            self.combined.pack(fill="both", expand=True)
        else:
            self.separate.pack(fill="both", expand=True)
        if self.current_dir:
            self.navigate(self.current_dir)

    def go_to_address(self):
        self.navigate(self.path_var.get())

    def refresh(self):
        here = self.current_dir or Path.home()
        self._load_roots()
        self.navigate(here)

    def up(self):
        if self.current_dir is not None:
            self.navigate(self.current_dir.parent)

    def _selected_path(self):
        if self.mode.get() == "combined":
            selected = self.alltree.selection()
            return self.all_paths.get(selected[0]) if selected else self.current_dir
        selected = self.files.selection()
        if selected:
            return self.file_paths.get(selected[0])
        selected = self.folders.selection()
        return self.folder_paths.get(selected[0]) if selected else self.current_dir

    def _double_file(self, event=None):
        item = self.files.identify_row(event.y) if event else None
        if item:
            self.files.selection_set(item)
            self.open_selected()

    def _double_all(self, event=None):
        item = self.alltree.identify_row(event.y) if event else None
        if item:
            self.alltree.selection_set(item)
            self.open_selected()

    def open_selected(self):
        path = self._selected_path()
        if path is None:
            messagebox.showinfo("Codex", "Выбери файл или папку.", parent=self.top)
            return
        try:
            if path.is_dir():
                self.navigate(path)
                return
            if not path.is_file():
                raise FileNotFoundError(path)
            filelist = getattr(self.bridge.editwin, "flist", None)
            if filelist is None or not hasattr(filelist, "open"):
                raise RuntimeError("Текущий IDLE не предоставляет FileList.open(). Открой файл через File → Open.")
            filelist.open(str(path))
        except (OSError, RuntimeError) as exc:
            messagebox.showerror("Codex — открыть", str(exc), parent=self.top)

    def copy_path(self):
        selected = self._selected_path()
        if selected is not None:
            self.bridge._clipboard_copy(str(selected))
            self.status_var.set(f"Путь скопирован: {selected}")

    def open_in_windows(self):
        selected = self._selected_path()
        if selected is None:
            return
        try:
            if os.name == "nt":
                if selected.is_file():
                    subprocess.Popen(["explorer.exe", "/select,", str(selected)])
                else:
                    os.startfile(str(selected))
            else:
                messagebox.showinfo("Codex", "Команда Проводника Windows доступна только в Windows.", parent=self.top)
        except OSError as exc:
            messagebox.showerror("Codex", str(exc), parent=self.top)

    def close(self):
        if self.bridge.file_browser is self:
            self.bridge.file_browser = None
        try:
            self.top.destroy()
        except tk.TclError:
            pass
