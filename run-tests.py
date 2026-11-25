import os
import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
import type_check_Larray
import interp_Larray
import type_check_Carray
import interp_Carray
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

type_check_Larray = type_check_Larray.TypeCheckLarray().type_check
type_check_Carray = type_check_Carray.TypeCheckCarray().type_check

typecheck_dict = {
    'source': type_check_Larray,
    'shrink': type_check_Larray,
    'resolve': type_check_Larray,
    'check_bounds': type_check_Larray,
    'expose_allocation': type_check_Larray,
    'remove_complex_operands': type_check_Larray,
    'explicate_control': type_check_Carray,
}

interp_Larray = interp_Larray.InterpLarray().interp
interp_Carray = interp_Carray.InterpCarray().interp
interp_dict = {
    'shrink': interp_Larray,
    'resolve': interp_Larray,
    'check_bounds': interp_Larray,
    'expose_allocation': interp_Larray,
    'remove_complex_operands': interp_Larray,
    'explicate_control': interp_Carray,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'remove_jumps': interp_x86,
    'patch_instructions': interp_x86,
    'prelude_and_conclusion': interp_x86,
}

if True:
    run_tests('array', compiler, 'array',
              typecheck_dict,
              interp_dict)
else: 
    run_one_test(os.getcwd() + '/tests/array/tuple-loop.py',
                 'array',
                 compiler,
                 'array',
                 typecheck_dict,
                 interp_dict)
