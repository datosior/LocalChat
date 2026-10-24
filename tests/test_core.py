"""Core LocalChat tests, no LM Studio server required."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("localchat", ROOT / "LocalChat_LMStudio.py")
localchat = importlib.util.module_from_spec(spec)
spec.loader.exec_module(localchat)


class LocalChatTests(unittest.TestCase):
    def test_valid_patch(self):
        answer = f"{localchat.BEGIN}\na = 2\n{localchat.END}\n"
        self.assertEqual(localchat.extract_fixed_code(answer, "a = 1\n"), "a = 2\n")

    def test_reject_unmarked_patch(self):
        with self.assertRaises(ValueError):
            localchat.extract_fixed_code("a = 2", "a = 1\n")

    def test_reject_invalid_python(self):
        with self.assertRaises(SyntaxError):
            localchat.extract_fixed_code(
                f"{localchat.BEGIN}\ndef bad(:\n{localchat.END}\n", "a = 1\n"
            )

    def test_preserve_crlf(self):
        source = "a = 1\r\nb = 2\r\n"
        answer = f"{localchat.BEGIN}\na = 2\nb = 2\n{localchat.END}\n"
        self.assertEqual(localchat.extract_fixed_code(answer, source), "a = 2\r\nb = 2\r\n")

    def test_backup_before_write(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            file = root / "example.py"
            file.write_bytes(b"value = 1\n")
            with patch.object(localchat.Path, "home", return_value=root):
                backup = localchat.safe_write_with_backup(
                    file, b"value = 1\n", "value = 2\n", "utf-8"
                )
            self.assertEqual(backup.read_bytes(), b"value = 1\n")
            self.assertEqual(file.read_bytes(), b"value = 2\n")

    def test_reject_changed_file(self):
        with tempfile.TemporaryDirectory() as folder:
            file = Path(folder) / "example.py"
            file.write_bytes(b"value = 3\n")
            with self.assertRaises(RuntimeError):
                localchat.safe_write_with_backup(
                    file, b"value = 1\n", "value = 2\n", "utf-8"
                )
            self.assertEqual(file.read_bytes(), b"value = 3\n")

    def test_reject_remote_api_path(self):
        with self.assertRaises(ValueError):
            localchat.request_local("https://example.org")

    def test_model_list_timeout(self):
        with patch.object(localchat, "request_local", return_value={
            "data": [{"id": "test-model"}]
        }) as request:
            self.assertEqual(localchat.available_models(), ["test-model"])
            self.assertEqual(request.call_args.kwargs["timeout"], 30)


if __name__ == "__main__":
    unittest.main()
