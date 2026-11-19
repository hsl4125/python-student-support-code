import unittest
from ast import *

from compiler import Compiler
from utils import parse


def has_input_int(node):
    return any(
        isinstance(n, Call)
        and isinstance(n.func, Name)
        and n.func.id == 'input_int'
        for n in walk(node)
    )


class PartialEvalTests(unittest.TestCase):
    def setUp(self):
        self.compiler = Compiler()

    def pe(self, source):
        return self.compiler.partial_eval(parse(source))

    def printed(self, expr_source):
        module = self.pe('print(' + expr_source + ')')
        self.assertEqual(len(module.body), 1)
        return module.body[0].value.args[0]

    def assert_printed(self, expr_source, expected_repr):
        self.assertEqual(repr(self.printed(expr_source)), expected_repr)

    def test_arithmetic_constants(self):
        self.assert_printed('1 + 2 + 3', 'Constant(6)')
        self.assert_printed('(1 - 2) - 3', 'Constant(-4)')
        self.assert_printed('-(-5)', 'Constant(5)')

    def test_compare_constants(self):
        self.assert_printed('1 < 2', 'Constant(True)')
        self.assert_printed('2 <= 1', 'Constant(False)')
        self.assert_printed('3 == 3', 'Constant(True)')
        self.assert_printed('3 != 3', 'Constant(False)')
        self.assert_printed('2 > 1', 'Constant(True)')
        self.assert_printed('1 >= 2', 'Constant(False)')

    def test_boolean_operators(self):
        self.assert_printed('not (1 < 2)', 'Constant(False)')
        self.assert_printed('True and (1 < 2)', 'Constant(True)')
        self.assert_printed('False and (1 < 2)', 'Constant(False)')
        self.assert_printed('True or (1 < 2)', 'Constant(True)')
        self.assert_printed('False or (1 < 2)', 'Constant(True)')

    def test_if_exp(self):
        self.assert_printed('1 if 1 < 2 else 0', 'Constant(1)')
        self.assert_printed('1 if 2 < 1 else 0', 'Constant(0)')

    def test_variable_test_is_preserved(self):
        self.assert_printed(
            '1 if x < 2 else 0',
            "IfExp(Compare(Name('x'), [Lt()], [Constant(2)]),"
            " Constant(1), Constant(0))",
        )

    def test_if_statement_constant_test_folds(self):
        module = self.pe('if 1 < 2:\n    print(1)\nelse:\n    print(2)\n')
        self.assertEqual(len(module.body), 1)
        self.assertEqual(repr(module.body[0].value.args[0]), 'Constant(1)')

    def test_if_statement_variable_test_is_preserved(self):
        module = self.pe('x = 3\nif x < 2:\n    print(1)\nelse:\n    print(2)\n')
        self.assertEqual(len(module.body), 2)
        if_stmt = module.body[1]
        self.assertIsInstance(if_stmt, If)
        self.assertEqual(
            repr(if_stmt.test),
            "Compare(Name('x'), [Lt()], [Constant(2)])",
        )

    def test_short_circuit_drops_unevaluated_operand(self):
        self.assertFalse(
            has_input_int(self.printed('1 if (False and input_int() < 0) else 0')))
        self.assertFalse(
            has_input_int(self.printed('1 if (True or input_int() < 0) else 0')))

    def test_short_circuit_keeps_evaluated_operand(self):
        self.assertTrue(
            has_input_int(self.printed('1 if (True and input_int() < 0) else 0')))
        self.assertTrue(
            has_input_int(self.printed('1 if (False or input_int() < 0) else 0')))


if __name__ == '__main__':
    unittest.main()
