import os
import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
import interp_Lif
import type_check_Lif
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

type_check_Lif = type_check_Lif.TypeCheckLif().type_check

typecheck_dict = {
    'source': type_check_Lif,
    'partial_eval': type_check_Lif,
    'shrink': type_check_Lif,
    'remove_complex_operands': type_check_Lif,
}

interpLif = interp_Lif.InterpLif().interp
interp_dict = {
    'partial_eval': interpLif,
    'shrink': interpLif,
    'remove_complex_operands': interpLif,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

if True:
    run_tests('if', compiler, 'if',
              typecheck_dict,
              interp_dict)
else:
    run_one_test(os.getcwd() + '/tests/var/zero.py',
                 'var',
                 compiler,
                 'var',
                 typecheck_dict,
                 interp_dict)
