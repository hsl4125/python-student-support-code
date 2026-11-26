import os
import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
import type_check_Carray
import interp_Carray
import type_check_Lfun
import interp_Lfun
import type_check_Cfun
import interp_Cfun
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

type_check_Lfun = type_check_Lfun.TypeCheckLfun().type_check
type_check_Cfun = type_check_Cfun.TypeCheckCfun().type_check
type_check_Carray = type_check_Carray.TypeCheckCarray().type_check

typecheck_dict = {
    'source': type_check_Lfun,
    'shrink': type_check_Lfun,
    'reveal_functions': type_check_Lfun,
    'resolve': type_check_Lfun,
    'check_bounds': type_check_Lfun,
    'limit_functions': type_check_Lfun,
    'expose_allocation': type_check_Lfun,
    'remove_complex_operands': type_check_Lfun,
    'explicate_control': type_check_Cfun,
}

interp_Lfun = interp_Lfun.InterpLfun().interp
interp_Cfun = interp_Cfun.InterpCfun().interp
interp_Carray = interp_Carray.InterpCarray().interp
interp_dict = {
    'shrink': interp_Lfun,
    'reveal_functions': interp_Lfun,
    'resolve': interp_Lfun,
    'check_bounds': interp_Lfun,
    'limit_functions': interp_Lfun,
    'expose_allocation': interp_Lfun,
    'remove_complex_operands': interp_Lfun,
    'explicate_control': interp_Cfun,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'remove_jumps': interp_x86,
    'patch_instructions': interp_x86,
    #'prelude_and_conclusion': interp_x86,
}

if True:
    run_tests('fun', compiler, 'fun',
              typecheck_dict,
              interp_dict)
else: 
    run_one_test(os.getcwd() + '/tests/fun/fun-tup-args.py',
                 'fun',
                 compiler,
                 'fun',
                 typecheck_dict,
                 interp_dict)
