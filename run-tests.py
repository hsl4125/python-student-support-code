import os
import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
import interp_Lwhile
import type_check_Lwhile
import type_check_Cif
import interp_Cif
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

type_check_Lwhile = type_check_Lwhile.TypeCheckLwhile().type_check
type_check_Cif = type_check_Cif.TypeCheckCif().type_check

typecheck_dict = {
    'source': type_check_Lwhile,
    #'partial_eval': type_check_Lwhile,
    'shrink': type_check_Lwhile,
    'remove_complex_operands': type_check_Lwhile,
    'explicate_control': type_check_Cif,
}

interp_Lwhile = interp_Lwhile.InterpLwhile().interp
interp_Cif = interp_Cif.InterpCif().interp
interp_dict = {
    #'partial_eval': interp_Lwhile,
    'shrink': interp_Lwhile,
    'remove_complex_operands': interp_Lwhile,
    'explicate_control': interp_Cif,
    #'select_instructions': interp_x86,
    #'assign_homes': interp_x86,
    #'remove_jumps': interp_x86,
    #'patch_instructions': interp_x86,
    #'prelude_and_conclusion': interp_x86,
}

if True:
    run_tests('while', compiler, 'while',
              typecheck_dict,
              interp_dict)
else:
    run_one_test(os.getcwd() + '/tests/while/while-1.py',
                 'while',
                 compiler,
                 'while',
                 typecheck_dict,
                 interp_dict)
