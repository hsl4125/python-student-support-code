import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
import type_check_Llambda
import interp_Llambda
import type_check_Clambda
import interp_Clambda
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86
from utils import run_tests, enable_tracing

enable_tracing()

compiler = compiler.Compiler()

type_check_Llambda = type_check_Llambda.TypeCheckLlambda().type_check
interp_Llambda = interp_Llambda.InterpLlambda().interp
type_check_Clambda = type_check_Clambda.TypeCheckClambda().type_check
interp_Clambda = interp_Clambda.InterpClambda().interp

typecheck_dict = {
    'source': type_check_Llambda,
    'shrink': type_check_Llambda,
    'uniquify': type_check_Llambda,
    'reveal_functions': type_check_Llambda,
    'resolve': type_check_Llambda,
    'check_bounds': type_check_Llambda,
    'convert_assignments': type_check_Llambda,
    'convert_to_closures': type_check_Llambda,
    'limit_functions': type_check_Llambda,
    'expose_allocation': type_check_Llambda,
    'remove_complex_operands': type_check_Llambda,
    'explicate_control': type_check_Clambda,
}

interp_dict = {
    'shrink': interp_Llambda,
    'uniquify': interp_Llambda,
    'reveal_functions': interp_Llambda,
    'resolve': interp_Llambda,
    'check_bounds': interp_Llambda,
    'convert_assignments': interp_Llambda,
    'convert_to_closures': interp_Llambda,
    'limit_functions': interp_Llambda,
    'expose_allocation': interp_Llambda,
    'remove_complex_operands': interp_Llambda,
    'explicate_control': interp_Clambda,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'remove_jumps': interp_x86,
    'patch_instructions': interp_x86,
    'prelude_and_conclusion': interp_x86,
}

if True:
    run_tests('lambda', compiler, 'lambda',
              typecheck_dict,
              interp_dict)
else:
    run_one_test(os.getcwd() + '/tests/lambda/lambda-shadow.py',
                 'lambda',
                 compiler,
                 'lambda',
                 typecheck_dict,
                 interp_dict)
