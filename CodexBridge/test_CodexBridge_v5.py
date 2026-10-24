"""Безопасный демонстрационный файл для CodexBridge 5.0.

Открой в IDLE, затем нажми Codex -> Запустить и проверить программу.
Намеренная ошибка: ZeroDivisionError в методе divide().
Codex сможет предложить проверку знаменателя после подтверждения.
"""

class Calculator:
    def divide(self, a, b):
        return a / b


def demonstration():
    calc = Calculator()
    print('Результат:', calc.divide(10, 0))


if __name__ == '__main__':
    demonstration()