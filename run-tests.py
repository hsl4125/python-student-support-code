import os
import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
#import interp_Lwhile
#import type_check_Lwhile
import type_check_Ctup
import interp_Ctup
import interp_Ltup
import type_check_Ltup
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

#type_check_Lwhile = type_check_Lwhile.TypeCheckLwhile().type_check
type_check_Ltuple = type_check_Ltup.TypeCheckLtup().type_check
type_check_Ctuple = type_check_Ctup.TypeCheckCtup().type_check

typecheck_dict = {
    'source': type_check_Ltuple,
    #'partial_eval': type_check_Lwhile,
    'shrink': type_check_Ltuple,
    'expose_allocation': type_check_Ltuple,
    'remove_complex_operands': type_check_Ltuple,
    'explicate_control': type_check_Ctuple,
}

#interp_Lwhile = interp_Lwhile.InterpLwhile().interp
interp_Ctuple = interp_Ctup.InterpCtup().interp
interp_Ltup = interp_Ltup.InterpLtup().interp
interp_dict = {
    #'partial_eval': interp_Lwhile,
    'shrink': interp_Ltup,
    'expose_allocation': interp_Ltup,
    'remove_complex_operands': interp_Ltup,
    'explicate_control': interp_Ctuple,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    #'remove_jumps': interp_x86,
    'patch_instructions': interp_x86,
    'prelude_and_conclusion': interp_x86,
}

if True:
    run_tests('tuple', compiler, 'tuple',
              typecheck_dict,
              interp_dict)
else:
    run_one_test(os.getcwd() + '/tests/tuple/tuple-loop.py',
                 'tuple',
                 compiler,
                 'tuple',
                 typecheck_dict,
                 interp_dict)
