import unittest
from ast import *

from compiler import Compiler
from x86_ast import Immediate, Instr, Jump, Reg, X86Program


class PreludeConclusionTests(unittest.TestCase):
    def setUp(self):
        self.compiler = Compiler()

    def test_main_jumps_to_start_and_conclusion_is_a_block(self):
        program = X86Program(
            {
                'block.3': [
                    Instr('movq', [Immediate(42), Reg('rcx')]),
                    Jump('conclusion'),
                ],
                'block.4': [
                    Instr('movq', [Immediate(0), Reg('rcx')]),
                    Jump('conclusion'),
                ],
                'start': [
                    Instr('movq', [Immediate(0), Reg('rax')]),
                    Jump('conclusion'),
                ],
            },
            stack_size=8,
            used_callee=[Reg('rbx')],
        )

        patched = self.compiler.prelude_and_conclusion(program)

        self.assertEqual(
            list(patched.body),
            ['main', 'start', 'block.3', 'block.4', 'conclusion'],
        )
        main = patched.body['main']
        self.assertEqual(
            [(i.instr, i.args) for i in main[:-1]],
            [
                ('pushq', (Reg('rbp'),)),
                ('movq', (Reg('rsp'), Reg('rbp'))),
                ('pushq', (Reg('rbx'),)),
                ('subq', (Immediate(8), Reg('rsp'))),
            ],
        )
        self.assertIsInstance(main[-1], Jump)
        self.assertEqual(main[-1].label, 'start')
        self.assertEqual(
            [(i.instr, i.args) for i in patched.body['conclusion']],
            [
                ('addq', (Immediate(8), Reg('rsp'))),
                ('popq', (Reg('rbx'),)),
                ('popq', (Reg('rbp'),)),
                ('retq', ()),
            ],
        )
        start = patched.body['start']
        self.assertEqual(
            [(i.instr, i.args) for i in start[:-1]],
            [('movq', (Immediate(0), Reg('rax')))],
        )
        self.assertIsInstance(start[-1], Jump)
        self.assertEqual(start[-1].label, 'conclusion')

    def test_no_callee_saved_or_stack_still_has_blocks(self):
        program = X86Program({'start': [Instr('retq', [])]})

        patched = self.compiler.prelude_and_conclusion(program)

        main = patched.body['main']
        self.assertEqual(
            [(i.instr, i.args) for i in main[:-1]],
            [
                ('pushq', (Reg('rbp'),)),
                ('movq', (Reg('rsp'), Reg('rbp'))),
                ('subq', (Immediate(0), Reg('rsp'))),
            ],
        )
        self.assertIsInstance(main[-1], Jump)
        self.assertEqual(main[-1].label, 'start')
        self.assertEqual(
            [(i.instr, i.args) for i in patched.body['conclusion']],
            [
                ('addq', (Immediate(0), Reg('rsp'))),
                ('popq', (Reg('rbp'),)),
                ('retq', ()),
            ],
        )

    def test_missing_start_block_raises(self):
        with self.assertRaises(ValueError):
            self.compiler.prelude_and_conclusion(X86Program({'main': []}))


if __name__ == '__main__':
    unittest.main()
