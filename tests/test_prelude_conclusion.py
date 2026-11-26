import unittest
from ast import *

from compiler import Compiler
from utils import IntType
from x86_ast import (
    Immediate,
    IndirectJump,
    Instr,
    Jump,
    Reg,
    TailJump,
    X86Program,
    X86ProgramDefs,
)


def instr_strings(instrs):
    return [str(i).strip() for i in instrs]


def make_def(name, blocks, stack_size=0, used_callee=None,
             root_stack_size=0):
    # An x86 function definition: the block dictionary lives in the body
    # field, and assign_homes_def attaches the per-function numbers.
    d = FunctionDef(name, [], blocks, None, IntType(), None)
    d.stack_size = stack_size
    d.used_callee = used_callee or []
    d.root_stack_size = root_stack_size
    return d


class PreludeConclusionTests(unittest.TestCase):
    def setUp(self):
        self.compiler = Compiler()

    def test_main_prelude_initializes_gc_and_conclusion_unwinds(self):
        main = make_def(
            'main',
            {
                'main_start': [
                    Instr('movq', [Immediate(0), Reg('rax')]),
                    Jump('main_conclusion'),
                ],
            },
            stack_size=8,
            used_callee=[Reg('rbx')],
        )

        program = self.compiler.prelude_and_conclusion(
            X86ProgramDefs([main]))

        self.assertIsInstance(program, X86Program)
        self.assertEqual(
            list(program.body),
            ['main', 'main_conclusion', 'main_start'],
        )
        self.assertEqual(
            instr_strings(program.body['main']),
            [
                'pushq %rbp',
                'movq %rsp, %rbp',
                'pushq %rbx',
                'subq $8, %rsp',
                'movq $65536, %rdi',
                'movq $16, %rsi',
                'callq initialize',
                'movq rootstack_begin(%rip), %r15',
                'jmp main_start',
            ],
        )
        self.assertEqual(
            instr_strings(program.body['main_conclusion']),
            [
                'addq $8, %rsp',
                'popq %rbx',
                'subq $0, %r15',
                'popq %rbp',
                'retq',
            ],
        )
        self.assertEqual(
            instr_strings(program.body['main_start']),
            ['movq $0, %rax', 'jmp main_conclusion'],
        )

    def test_non_main_function_has_no_initialize(self):
        # A callee adds its own root frame on top of the caller's and zeroes
        # only the new slots; only main calls initialize.
        f = make_def(
            'f',
            {
                'f_start': [
                    Instr('movq', [Immediate(1), Reg('rax')]),
                    Jump('f_conclusion'),
                ],
            },
            root_stack_size=16,
        )

        program = self.compiler.prelude_and_conclusion(
            X86ProgramDefs([f]))

        self.assertEqual(
            list(program.body),
            ['f', 'f_conclusion', 'f_start'],
        )
        self.assertEqual(
            instr_strings(program.body['f']),
            [
                'pushq %rbp',
                'movq %rsp, %rbp',
                'subq $0, %rsp',
                'movq $0, 0(%r15)',
                'addq $8, %r15',
                'movq $0, 0(%r15)',
                'addq $8, %r15',
                'jmp f_start',
            ],
        )
        self.assertEqual(
            instr_strings(program.body['f_conclusion']),
            [
                'addq $0, %rsp',
                'subq $16, %r15',
                'popq %rbp',
                'retq',
            ],
        )

    def test_tail_jump_is_expanded_into_epilogue_and_indirect_jump(self):
        main = make_def(
            'main',
            {
                'main_start': [
                    Instr('movq', [Immediate(1), Reg('rax')]),
                    TailJump(Reg('rax'), 0),
                ],
            },
            stack_size=8,
            used_callee=[Reg('rbx')],
        )

        program = self.compiler.prelude_and_conclusion(
            X86ProgramDefs([main]))

        self.assertEqual(
            instr_strings(program.body['main_start']),
            [
                'movq $1, %rax',
                'addq $8, %rsp',
                'popq %rbx',
                'subq $0, %r15',
                'popq %rbp',
                'jmp *%rax',
            ],
        )
        self.assertNotIn(
            'tailjmp %rax',
            instr_strings(program.body['main_start']),
        )

    def test_large_root_stack_is_zeroed_slot_by_slot(self):
        root_stack_size = 32768
        main = make_def(
            'main',
            {'main_start': [Instr('retq', [])]},
            root_stack_size=root_stack_size,
        )

        program = self.compiler.prelude_and_conclusion(
            X86ProgramDefs([main]))

        main_instrs = instr_strings(program.body['main'])
        self.assertIn('movq $65536, %rdi', main_instrs)
        self.assertNotIn('rep stosq', main_instrs)
        self.assertEqual(
            main_instrs.count('movq $0, 0(%r15)'),
            root_stack_size // 8,
        )
        self.assertEqual(
            main_instrs.count('addq $8, %r15'),
            root_stack_size // 8,
        )
        self.assertEqual(
            instr_strings(program.body['main_conclusion'])[-1],
            'retq',
        )
        self.assertIn(
            'subq $32768, %r15',
            instr_strings(program.body['main_conclusion']),
        )

    def test_main_block_comes_first(self):
        f = make_def('f', {'f_start': [Instr('retq', [])]})
        main = make_def('main', {'main_start': [Instr('retq', [])]})

        program = self.compiler.prelude_and_conclusion(
            X86ProgramDefs([f, main]))

        labels = list(program.body)
        self.assertEqual(labels[0], 'main')
        self.assertIn('f', labels)
        self.assertIn('f_conclusion', labels)

    def test_missing_start_block_raises(self):
        main = make_def('main', {'some_block': [Instr('retq', [])]})
        with self.assertRaises(ValueError):
            self.compiler.prelude_and_conclusion(X86ProgramDefs([main]))


if __name__ == '__main__':
    unittest.main()
