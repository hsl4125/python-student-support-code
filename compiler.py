import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict

Binding = Tuple[Name, expr]
Temporaries = List[Binding]


class Compiler:

    """
    ############################################################################
    #  Partial Evaluator (old)
    ############################################################################

    def pe_neg(self, e: expr) -> expr:
        match e:
            case Constant(n):
                return Constant(neg64(n))
            case _:
                return UnaryOp(USub(), e)

    def pe_add(self, l: expr, r: expr) -> expr:
        match (l, r):
            case (Constant(a), Constant(b)):
                return Constant(add64(a, b))
            case _:
                return BinOp(l, Add(), r)

    def pe_exp(self, e: expr) -> expr:
        match e:
            case UnaryOp(USub(), exp):
                return self.pe_neg(self.pe_exp(exp))
            case BinOp(l, Add(), r):
                return self.pe_add(self.pe_exp(l), self.pe_exp(r))
            case BinOp(l, Sub(), r):
                return self.pe_add(self.pe_exp(l), self.pe_neg(self.pe_exp(r)))
            case _:
                #raise Exception('error in pe_exp, unexpected ' + repr(e))
                return e

    def pe_stmt(self, s: stmt) -> stmt:
        match s:
            case Expr(Call(Name('print'), [exp])):
                e = self.pe_exp(exp)
                return Expr(Call(Name('print'), [e]))
            case Expr(exp):
                return Expr(self.pe_exp(exp))
            case Assign([Name(id)], exp):
                e = self.pe_exp(exp)
                return Assign([Name(id)], e)
            case _:
                #raise Exception('error in pe_stmt, unexpected ' + repr(s))
                return s

    def partial_eval(self, p: Module) -> Module:
        match p:
            case Module(body):
                stmts = []
                for stmt in body:
                    stmts.append(self.pe_stmt(stmt))
                return Module(stmts)
            case _:
                raise Exception('error in partial_eval_old, unexpected ' + repr(p))
    """

    ############################################################################
    #  Partial Evaluator
    ############################################################################

    def residual(self, e: expr) -> expr:
        match e:
            case BinOp(l, Add(), Constant(n)):
                return BinOp(Constant(n), Add(), self.residual(l))
            case BinOp(l, Sub(), r):
                return BinOp(self.residual(l), Add(), UnaryOp(USub(), self.residual(r)))
            case UnaryOp(USub(), exp):
                return UnaryOp(USub(), self.residual(exp))
            case _:
                return e

    def pe_neg(self, e: expr) -> expr:
        match e:
            case Constant(n):
                return Constant(neg64(n))
            case _:
                return UnaryOp(USub(), e)

    def pe_add(self, l: expr, r: expr) -> expr:
        match (l, r):
            case (Constant(a), Constant(b)):
                return Constant(add64(a, b))
            case (Constant(a), BinOp(Constant(b), Add(), rest)):
                return self.pe_add(Constant(add64(a, b)), rest)
            case _:
                return BinOp(l, Add(), r)

    def pe_exp(self, e: expr) -> expr:
        match e:
            case UnaryOp(USub(), exp):
                return self.pe_neg(self.residual(exp))
            case BinOp(l, Add(), r):
                return self.pe_add(self.residual(l), self.residual(r))
            case BinOp(l, Sub(), r):
                return self.pe_add(self.residual(l), self.pe_neg(self.residual(r)))
            case _:
                #raise Exception('error in pe_exp, unexpected ' + repr(e))
                return e

    def pe_stmt(self, s: stmt) -> stmt:
        match s:
            case Expr(Call(Name('print'), [exp])):
                e = self.pe_exp(exp)
                return Expr(Call(Name('print'), [e]))
            case Expr(exp):
                return Expr(self.pe_exp(exp))
            case Assign([Name(id)], exp):
                e = self.pe_exp(exp)
                return Assign([Name(id)], e)
            case _:
                #raise Exception('error in pe_stmt, unexpected ' + repr(s))
                return s

    def partial_eval(self, p: Module) -> Module:
        match p:
            case Module(body):
                stmts = []
                for stmt in body:
                    stmts.append(self.pe_stmt(stmt))
                return Module(stmts)
            case _:
                raise Exception('error in partial_eval, unexpected ' + repr(p))

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
            case Expr(Call(Name('print'), [exp])):
                (expr, temporaries) = self.rco_exp(exp, True)
                stmts = resolve_temporaries(temporaries)
                call = Expr(Call(Name('print'), [expr]))
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
        match e:
            case Constant(value):
                return Immediate(value)
            case Name(id):
                return Variable(id)
            case _:
                raise Exception('error in select_arg, unexpected ' + repr(e))

    def select_exp(self, e: expr, target: arg | None) -> List[instr]:
        match e:
            case Constant(_) | Name(_):
                if target is None:
                    return []
                src = self.select_arg(e)
                if src == target:
                    return []
                return [Instr('movq', [src, target])]
            case Call(Name('input_int'), []):
                instrs = [Callq('read_int', 0)]
                if target is not None:
                    instrs.append(Instr('movq', [Reg('rax'), target]))
                return instrs
            case UnaryOp(USub(), atm):
                if target is None:
                    return []
                src = self.select_arg(atm)
                instrs = []
                if src != target:
                    instrs.append(Instr('movq', [src, target]))
                instrs.append(Instr('negq', [target]))
                return instrs
            case BinOp(left, Add(), right):
                if target is None:
                    return []
                left_arg = self.select_arg(left)
                right_arg = self.select_arg(right)
                if target == left_arg or target == right_arg:
                    other = right_arg if target == left_arg else left_arg
                    return [Instr('addq', [other, target])]
                return [
                    Instr('movq', [left_arg, target]),
                    Instr('addq', [right_arg, target]),
                ]
            case BinOp(left, Sub(), right):
                if target is None:
                    return []
                left_arg = self.select_arg(left)
                right_arg = self.select_arg(right)
                if target == right_arg and target != left_arg:
                    return [
                        Instr('movq', [left_arg, Reg('rax')]),
                        Instr('subq', [right_arg, Reg('rax')]),
                        Instr('movq', [Reg('rax'), target]),
                    ]
                instrs = []
                if left_arg != target:
                    instrs.append(Instr('movq', [left_arg, target]))
                instrs.append(Instr('subq', [right_arg, target]))
                return instrs
            case _:
                raise Exception('error in select_exp, unexpected ' + repr(e))

    def select_stmt(self, s: stmt) -> List[instr]:
        Instrs = []
        match s:
            case Expr(Call(Name('print'), [exp])):
                src = self.select_arg(exp)
                mov = Instr('movq', [src, Reg('rdi')])
                call = Callq('print_int', 1)
                Instrs.append(mov)
                Instrs.append(call)
                return Instrs
            case Expr(exp):
                return self.select_exp(exp, None)
            case Assign([Name(id)], exp):
                return self.select_exp(exp, Variable(id))
            case _:
                raise Exception('error in select_stmt, unexpected ' + repr(s))

    def select_instructions(self, p: Module) -> X86Program:
        match p:
            case Module(body):
                Instrs = []
                for stmt in body:
                    s = self.select_stmt(stmt)
                    Instrs += s
                return X86Program({'main' : Instrs})
            case _:
                raise Exception('error in select_instructions, unexpected ' + repr(p))

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case Variable(id) as k:
                v = home.get(k)
                if v != None:
                    return v
                else:
                    size = len(home)
                    offset = -8 * size - 8
                    v = Deref('rbp', offset)
                    home[k] = v
                    return v
            case _:
                return a

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        match i:
            case  Instr(iname, [src, dst]) if iname in ['addq', 'subq', 'movq'] :
                src = self.assign_homes_arg(src, home)
                dst = self.assign_homes_arg(dst, home)
                return Instr(iname, [src, dst])
            case Instr(iname, [dst]) if iname in ['negq']:
                dst = self.assign_homes_arg(dst, home)
                return Instr(iname, [dst])
            case _:
                return i

    def assign_homes(self, p: X86Program) -> X86Program:
        def set_stack_size():
            size = len(home)
            stack_size = size * 8
            if stack_size % 16 != 0:
                stack_size += 8
            p.stack_size = stack_size

        match p:
            case X86Program(body) if isinstance(body, dict):
                home = {}
                for name, block in body.items():
                    instrs = []
                    for i in block:
                        newi = self.assign_homes_instr(i, home)
                        instrs.append(newi)
                    body[name] = instrs

                set_stack_size()
                return p
            case _:
                raise Exception('error in assign_homes, unexpected ' + repr(p))

    # Liveness Analysis
    # Lafter(k) = Lbefore(k + 1)
    # Lafter(n) = ∅  (last instruction)
    # Lbefore(k) = (Lafter(k) − W(k)) ∪ R(k)
    # R(K): read instruction I(k)
    # W(K): write instruction I(k)
    def uncover_live(self, s: List[instr]) -> dict[instr, set[location]]:
        def operand_locations(l: arg) -> set[location]:
            match l:
                case Variable(id): return {l}
                case Reg(r): return {l}
                case Deref(reg, offset): return {Reg(reg)}
                case _ : return set()

        def written_locations(l: arg) -> set[location]:
            match l:
                case Variable(id): return {l}
                case Reg(r): return {l}
                case _ : return set()

        def address_base_locations(l: arg) -> set[location]:
            match l:
                case Deref(reg, _): return {Reg(reg)}
                case _ : return set()

        def R(i: instr) -> set[location]:
            match i:
                case Instr(iname, [src, dst]) if iname in ['addq', 'subq']:
                    return operand_locations(src) | operand_locations(dst)
                case Instr('movq', [src, dst]):
                    return operand_locations(src) | address_base_locations(dst)
                case Instr('negq', [dst]):
                    return operand_locations(dst)
                case Instr('pushq', [src]):
                    return {Reg('rsp')} | operand_locations(src)
                case Instr('popq', [dst]):
                    return {Reg('rsp')} | address_base_locations(dst)
                case Callq(_, n):
                    passed = [Reg('rdi'), Reg('rsi'), Reg('rdx'), Reg('rcx'), Reg('r8'), Reg('r9')]
                    return set(passed[:n])
                case Instr('retq', []):
                    return {Reg('rsp')}
                case _:
                    return set()

        def W(i: instr) -> set[location]:
            match i:
                case Instr(iname, [_, dst]) if iname in ['addq', 'subq']:
                    return written_locations(dst)
                case Instr('movq', [_, dst]):
                    return written_locations(dst)
                case Instr('negq', [dst]):
                    return written_locations(dst)
                case Instr('pushq', [dst]):
                    return {Reg('rsp')}
                case Instr('popq', [dst]):
                    return {Reg('rsp')} | written_locations(dst)
                case Callq(_, _):
                    rs = [Reg('rax'), Reg('rcx'), Reg('rdx'), Reg('rsi'), Reg('rdi'), Reg('r8'), Reg('r9'), Reg('r10'), Reg('r11')]
                    return set(rs)
                case Instr('retq', []):
                    return {Reg('rsp')}
                case _:
                    return set()

        live_after = {}
        if not s:
            return live_after
        after_i = set()
        before_i = set()

        for i in reversed(s):
            before_i = after_i.difference(W(i)) | R(i)
            live_after[i] = after_i
            after_i = before_i
        
        return live_after

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        MIN_INT32 = -(1<<31)
        MAX_INT32 = (1<<31)-1
        instrs = []
        match i:
            case Instr('movq', [Deref() as src, Deref() as dst]) :
                instrs.append(Instr('movq', [src, Reg('rax')]))
                instrs.append(Instr('movq', [Reg('rax'), dst]))
            case Instr(iname, [Deref() as src, Deref() as dst]) if iname in ['addq', 'subq']:
                instrs.append(Instr('movq', [src, Reg('rax')]))
                instrs.append(Instr(iname, [Reg('rax'), dst]))
            case Instr('movq', [Immediate(n), dst]) if not (MIN_INT32 <= n <= MAX_INT32):
                instrs.append(Instr('movq', [Immediate(n), Reg('rax')]))
                instrs.append(Instr('movq', [Reg('rax'), dst]))
            case _:
                instrs.append(i)
        return instrs

    def patch_instructions(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                for name, block in body.items():
                    instrs = []
                    for i in block:
                        instrs += self.patch_instr(i)
                    body[name] = instrs
                return p
            case _:
                raise Exception('error in patch_instructions, unexpected ' + repr(p))

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        def prelude(stack_size) -> List[instr]:
            return [
                Instr('pushq', [Reg('rbp')]),
                Instr('movq', [Reg('rsp'), Reg('rbp')]),
                Instr('subq', [Immediate(stack_size), Reg('rsp')])
            ]

        def conclusion(stack_size) -> List[instr]:
            return [
                Instr('addq', [Immediate(stack_size), Reg('rsp')]),
                Instr('popq', [Reg('rbp')]),
                Instr('retq', [])
            ]

        match p:
            case X86Program(body):
                instrs = body.get('main')
                if instrs == None:
                    raise Exception('error in prelude_and_conclusion, main block is empty')
                main_instrs = prelude(p.stack_size)
                main_instrs += instrs
                main_instrs += conclusion(p.stack_size)
                body['main'] = main_instrs
                return p
            case _:
                raise Exception('error in prelude_and_conclusion, unexpected ' + repr(p))
