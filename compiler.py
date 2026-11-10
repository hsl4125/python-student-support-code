import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict

Binding = Tuple[Name, expr]
Temporaries = List[Binding]


class Compiler:

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic : bool) -> Tuple[expr, Temporaries]:
        def new_tmp_id() -> Name:
            return Name(generate_name('tmp'))
        match e:
            case Constant(value) as constant:
                return (constant, [])
            case Name(id) as var:
                return (var, [])
            case Call(Name('input_int'), []) as call:
                if need_atomic:
                    new_id = new_tmp_id()
                    binding = (new_id, call)
                    return (new_id, [binding])
                else:
                    return (call, [])
            case UnaryOp(USub(), exp):
                if need_atomic:
                    new_id = new_tmp_id()
                    (name, bindings) = self.rco_exp(exp, True)
                    binding = (new_id, UnaryOp(USub(), name))
                    bindings.append(binding)
                    return (new_id, bindings)
                else:
                    (name, bindings) = self.rco_exp(exp, True)
                    return (UnaryOp(USub(), name), bindings)
            case BinOp(left, Add() as op, right) | BinOp(left, Sub() as op, right):
                if need_atomic:
                    new_id = new_tmp_id()
                    (left_name, left_bindings) = self.rco_exp(left, True)
                    (right_name, right_bindings) = self.rco_exp(right, True)
                    bindings = left_bindings + right_bindings
                    binding = (new_id, BinOp(left_name, op, right_name))
                    bindings.append(binding)
                    return (new_id, bindings)
                else:
                    (left_name, left_bindings) = self.rco_exp(left, True)
                    (right_name, right_bindings) = self.rco_exp(right, True)
                    bindings = left_bindings + right_bindings
                    return (BinOp(left_name, op, right_name), bindings)
            case _:
                raise Exception('error in rco_exp, unexpected ' + repr(e))


    def rco_stmt(self, s: stmt) -> List[stmt]:
        def resolve_temporaries(temporaries) -> List[stmt]:
            stmts = []
            for (name, expr) in temporaries:
                stmt = Assign([name], expr)
                stmts.append(stmt)
            return stmts
        match s:
            case Expr(Call(Name('print'), exps)):
                stmts = []
                args = []
                for exp in exps:
                    (expr, temporaries) = self.rco_exp(exp, True)
                    s = resolve_temporaries(temporaries)
                    stmts += s
                    args.append(expr)
                call = Expr(Call(Name('print'), args))
                stmts.append(call)
                return stmts
            case Expr(exp):
                (expr, temporaries) = self.rco_exp(exp, False)
                stmts = resolve_temporaries(temporaries)
                stmts.append(Expr(expr))
                return stmts
            case Assign([Name(id)], exp):
                (expr, temporaries) = self.rco_exp(exp, True)
                stmts = resolve_temporaries(temporaries)
                assign = Assign([Name(id)], expr)
                stmts.append(assign)
                return stmts
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(s))
        

    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(body):
                stmts = []
                for stmt in body:
                    s = self.rco_stmt(stmt)
                    stmts += s
                return Module(stmts)
            case _:
                raise Exception('error in remove_complex_operands, unexpected ' + repr(p))

    ############################################################################
    # Select Instructions
    ############################################################################

    # The expression e passed to select_arg should furthermore be an atom.
    # (But there is no type for atoms, so the type of e is given as expr.)
    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        pass        

    def select_stmt(self, s: stmt) -> List[instr]:
        # YOUR CODE HERE
        pass        

    def select_instructions(self, p: Module) -> X86Program:
        # YOUR CODE HERE
        pass        

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        pass        

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        # YOUR CODE HERE
        pass        

    def assign_homes(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        # YOUR CODE HERE
        pass        

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        
