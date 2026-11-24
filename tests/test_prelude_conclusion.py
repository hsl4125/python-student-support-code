import unittest
from ast import *

from compiler import Compiler
from x86_ast import Immediate, Instr, Jump, Reg, X86Program


def instr_strings(instrs):
    return [str(i).strip() for i in instrs]


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
        # main sets up the root stack for the garbage collector, then jumps
        # to the start block instead of running the program directly.
        self.assertEqual(
            instr_strings(patched.body['main']),
            [
                'pushq %rbp',
                'movq %rsp, %rbp',
                'pushq %rbx',
                'subq $8, %rsp',
                'movq $65536, %rdi',
                'movq $16, %rsi',
                'callq initialize',
                'movq rootstack_begin(%rip), %r15',
                'jmp start',
            ],
        )
        self.assertEqual(
            instr_strings(patched.body['conclusion']),
            [
                'subq $0, %r15',
                'addq $8, %rsp',
                'popq %rbx',
                'popq %rbp',
                'retq',
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

        self.assertEqual(
            instr_strings(patched.body['main']),
            [
                'pushq %rbp',
                'movq %rsp, %rbp',
                'subq $0, %rsp',
                'movq $65536, %rdi',
                'movq $16, %rsi',
                'callq initialize',
                'movq rootstack_begin(%rip), %r15',
                'jmp start',
            ],
        )
        self.assertEqual(
            instr_strings(patched.body['conclusion']),
            [
                'subq $0, %r15',
                'addq $0, %rsp',
                'popq %rbp',
                'retq',
            ],
        )

    def test_root_stack_slots_are_zeroed(self):
        # Two root slots (16 bytes) must be zeroed before the program starts;
        # %r15 is advanced past them, and the conclusion unwinds it.
        program = X86Program(
            {'start': [Instr('retq', [])]},
            stack_size=8,
            used_callee=[Reg('rbx')],
            root_stack_size=16,
        )

        patched = self.compiler.prelude_and_conclusion(program)

        self.assertEqual(
            instr_strings(patched.body['main']),
            [
                'pushq %rbp',
                'movq %rsp, %rbp',
                'pushq %rbx',
                'subq $8, %rsp',
                'movq $65536, %rdi',
                'movq $16, %rsi',
                'callq initialize',
                'movq rootstack_begin(%rip), %r15',
                'movq %r15, %rdi',
                'movq $0, %rax',
                'movq $2, %rcx',
                'rep stosq',
                'addq $16, %r15',
                'jmp start',
            ],
        )
        self.assertEqual(
            instr_strings(patched.body['conclusion']),
            [
                'subq $16, %r15',
                'addq $8, %rsp',
                'popq %rbx',
                'popq %rbp',
                'retq',
            ],
        )

    def test_large_root_stack_still_uses_minimum_size(self):
        # ROOTSTACK_INIT_SIZE (8192 slots) is a floor: a larger
        # root_stack_size must be rounded up to a multiple of 64 and still
        # leave a strict margin below rootstack_end.  Zeroing stays a single
        # REP STOSQ regardless of the slot count.
        root_stack_size = 32768
        program = X86Program(
            {'start': [Instr('retq', [])]},
            root_stack_size=root_stack_size,
        )

        patched = self.compiler.prelude_and_conclusion(program)

        main = instr_strings(patched.body['main'])
        self.assertIn('movq $65536, %rdi', main)
        self.assertIn('movq $4096, %rcx', main)
        self.assertIn('rep stosq', main)
        self.assertIn('addq $32768, %r15', main)
        self.assertFalse(
            [s for s in main
             if s.startswith('movq $0, ') and s.endswith('(%r15)')])
        self.assertEqual(
            instr_strings(patched.body['conclusion'])[0],
            'subq $32768, %r15',
        )

    def test_missing_start_block_raises(self):
        with self.assertRaises(ValueError):
            self.compiler.prelude_and_conclusion(X86Program({'main': []}))


if __name__ == '__main__':
    unittest.main()
