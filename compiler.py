import ast
from ast import *
import typing
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict
from graph import *

Binding = Tuple[Name, expr]
Temporaries = List[Binding]


@dataclass
class Promise:
    fun: typing.Callable[[], list[stmt]]
    cache: typing.Optional[list[stmt]] = None
    def force(self) -> list[stmt]:
        if self.cache is None:
            self.cache = self.fun()
        return self.cache


# A "promise" is either an already-computed list of statements or a delayed
# computation (Promise) that produces one when forced.
Code = typing.Union[list[stmt], Promise]


def force(promise: Code) -> list[stmt]:
    return promise.force() if isinstance(promise, Promise) else promise


def create_block(promise: Code, basic_blocks: dict[str, list[stmt]]) -> Promise:
    def delay() -> list[stmt]:
        stmts = force(promise)
        match stmts:
            case [Goto(l)]:
                return stmts
            case _:
                label = label_name(generate_name('block'))
                basic_blocks[label] = stmts
                return [Goto(label)]
    return Promise(delay)


class Compiler:

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

    def pe_cmp(self, op, l: expr, r: expr) -> expr:
        match (l, r):
            case (Constant(a), Constant(b)):
                match op:
                    case Eq(): return Constant(a == b)
                    case NotEq(): return Constant(a != b)
                    case Lt(): return Constant(a < b)
                    case LtE(): return Constant(a <= b)
                    case Gt(): return Constant(a > b)
                    case GtE(): return Constant(a >= b)
            case _:
                pass
        return Compare(l, [op], [r])

    def pe_exp(self, e: expr) -> expr:
        match e:
            case Constant(_) | Name(_):
                return e
            case UnaryOp(USub(), exp):
                return self.pe_neg(self.residual(self.pe_exp(exp)))
            case UnaryOp(Not(), exp):
                inner = self.pe_exp(exp)
                match inner:
                    case Constant(True): return Constant(False)
                    case Constant(False): return Constant(True)
                    case UnaryOp(Not(), operand): return operand
                    case _: return UnaryOp(Not(), inner)
            case BinOp(left, Add(), right):
                return self.pe_add(self.residual(self.pe_exp(left)),
                                   self.residual(self.pe_exp(right)))
            case BinOp(left, Sub(), right):
                return self.pe_add(self.residual(self.pe_exp(left)),
                                   self.pe_neg(self.residual(self.pe_exp(right))))
            case Compare(left, [op], [right]):
                return self.pe_cmp(op, self.pe_exp(left), self.pe_exp(right))
            case BoolOp(And(), [left, right]):
                l = self.pe_exp(left)
                r = self.pe_exp(right)
                match l:
                    case Constant(True): return r
                    case Constant(False): return Constant(False)
                    case _: return BoolOp(And(), [l, r])
            case BoolOp(Or(), [left, right]):
                l = self.pe_exp(left)
                r = self.pe_exp(right)
                match l:
                    case Constant(True): return Constant(True)
                    case Constant(False): return r
                    case _: return BoolOp(Or(), [l, r])
            case IfExp(test, body, orelse):
                t = self.pe_exp(test)
                b = self.pe_exp(body)
                o = self.pe_exp(orelse)
                match t:
                    case Constant(True): return b
                    case Constant(False): return o
                    case _: return IfExp(t, b, o)
            case _:
                return e

    def pe_stmts(self, stmts: List[stmt]) -> List[stmt]:
        result = []
        for s in stmts:
            result.extend(self.pe_stmt(s))
        return result

    def pe_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Expr(Call(Name('print'), [exp])):
                return [Expr(Call(Name('print'), [self.pe_exp(exp)]))]
            case Expr(exp):
                return [Expr(self.pe_exp(exp))]
            case Assign([Name(id)], exp):
                return [Assign([Name(id)], self.pe_exp(exp))]
            case If(test, body, orelse):
                t = self.pe_exp(test)
                b = self.pe_stmts(body)
                o = self.pe_stmts(orelse)
                match t:
                    case Constant(True): return b
                    case Constant(False): return o
                    case _: return [If(t, b, o)]
            case _:
                return [s]

    def partial_eval(self, p: Module) -> Module:
        match p:
            case Module(body):
                return Module(self.pe_stmts(body))
            case _:
                raise Exception('error in partial_eval, unexpected ' + repr(p))

    ############################################################################
    # Shrink
    ############################################################################
    def shrink_exp(self, e: expr) -> expr:
        match  e:
            case BoolOp(And(),[e1, e2]):
                return IfExp(self.shrink_exp(e1), self.shrink_exp(e2), Constant(False))
            case BoolOp(Or(),[e1, e2]):
                return IfExp(self.shrink_exp(e1), Constant(True), self.shrink_exp(e2))
            case UnaryOp(op, operand):
                return UnaryOp(op, self.shrink_exp(operand))
            case BinOp(left, op, right):
                return BinOp(self.shrink_exp(left), op, self.shrink_exp(right))
            case Compare(left, ops, comparators):
                return Compare(self.shrink_exp(left), ops,
                               [self.shrink_exp(comparator) for comparator in comparators])
            case IfExp(test, body, orelse):
                return IfExp(self.shrink_exp(test), self.shrink_exp(body),
                             self.shrink_exp(orelse))
            case Call(func, args):
                return Call(self.shrink_exp(func),
                            [self.shrink_exp(arg) for arg in args])
            case Constant(_) | Name(_):
                return e
            case _:
                return e

    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case Expr(Call(Name('print'),[exp])):
                return Expr(Call(Name('print'), [self.shrink_exp(exp)]))
            case Expr(exp):
                return Expr(self.shrink_exp(exp))
            case Assign([Name(id)], exp):
                return Assign([Name(id)], self.shrink_exp(exp))
            case If(exp, body, orelse):
                return If(self.shrink_exp(exp), [self.shrink_stmt(s) for s in body], [self.shrink_stmt(s) for s in orelse])
            case _:
                raise Exception('error in shrink_stmt, unexpected ' + repr(s))

    def shrink(self, p: Module) -> Module:
        match p:
            case Module(body):
                stmts = []
                for stmt in body:
                    s = self.shrink_stmt(stmt)
                    stmts.append(s)
                return Module(stmts)
            case _:
                raise Exception('error in shrink, unexpected ' + repr(p))

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
        def finish_rco(exp: expr, bindings: Temporaries):
            if need_atomic:
                new_id = Name(generate_name('tmp'))
                return (new_id, bindings + [(new_id, exp)])
            return (exp, bindings)

        match e:
            case Constant(value) as constant:
                return (constant, [])
            case Name(id) as var:
                return (var, [])
            case Call(Name('input_int'), []) as call:
                return finish_rco(call, [])
            case UnaryOp(op, exp):
                (operand, bindings) = self.rco_exp(exp, True)
                result = UnaryOp(op, operand)
                return finish_rco(result, bindings)
            case BinOp(left, op, right):
                (left_name, left_bindings) = self.rco_exp(left, True)
                (right_name, right_bindings) = self.rco_exp(right, True)
                result = BinOp(left_name, op, right_name)
                return finish_rco(result, left_bindings + right_bindings)
            case Compare(left, ops, comparators):
                (left_name, left_bindings) = self.rco_exp(left, True)
                reduced = []
                bindings = left_bindings
                for comparator in comparators:
                    (comp_name, comp_bindings) = self.rco_exp(comparator, True)
                    reduced.append(comp_name)
                    bindings.extend(comp_bindings)
                result = Compare(left_name, ops, reduced)
                return finish_rco(result, bindings)
            case IfExp(test, body, orelse):
                (test_name, test_bindings) = self.rco_exp(test, False)
                (body_name, body_bindings) = self.rco_exp(body, False)
                (orelse_name, orelse_bindings) = self.rco_exp(orelse, False)
                result = IfExp(
                    make_begin(test_bindings, test_name),
                    make_begin(body_bindings, body_name),
                    make_begin(orelse_bindings, orelse_name),
                )
                return finish_rco(result, [])
            case _:
                raise Exception('error in rco_exp, unexpected ' + repr(e))

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Expr(Call(Name('print'), [exp])):
                (expr, temporaries) = self.rco_exp(exp, True)
                stmts = make_assigns(temporaries)
                stmts.append(Expr(Call(Name('print'), [expr])))
                return stmts
            case Expr(exp):
                (expr, temporaries) = self.rco_exp(exp, False)
                stmts = make_assigns(temporaries)
                stmts.append(Expr(expr))
                return stmts
            case Assign([Name(id)], exp):
                (expr, temporaries) = self.rco_exp(exp, False)
                stmts = make_assigns(temporaries)
                stmts.append(Assign([Name(id)], expr))
                return stmts
            case If(test, body, orelse):
                (test_expr, test_bindings) = self.rco_exp(test, False)
                body_stmts = []
                for stmt in body:
                    body_stmts.extend(self.rco_stmt(stmt))
                orelse_stmts = []
                for stmt in orelse:
                    orelse_stmts.extend(self.rco_stmt(stmt))
                stmts = make_assigns(test_bindings)
                stmts.append(If(test_expr, body_stmts, orelse_stmts))
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
    # Explicate Control
    ############################################################################
    
    def explicate_stmts(
        self, stmts: list[stmt], cont: Code, basic_blocks: dict[str, list[stmt]]
    ) -> Code:
        for s in reversed(stmts):
            cont = self.explicate_stmt(s, cont, basic_blocks)
        return cont

    def explicate_effect(
        self, e: expr, cont: Code, basic_blocks: dict[str, list[stmt]]
    ) -> Code:
        match e:
            case Constant(_) | Name(_):
                return cont
            case Call(Name('input_int'), []) as call:
                return [Expr(call)] + force(cont)
            case Begin(stmts, result):
                cont = self.explicate_effect(result, cont, basic_blocks)
                return self.explicate_stmts(stmts, cont, basic_blocks)
            case IfExp(test, body, orelse):
                cont_block = create_block(cont, basic_blocks)
                thn = Promise(lambda: force(self.explicate_effect(body, cont_block, basic_blocks)))
                els = Promise(lambda: force(self.explicate_effect(orelse, cont_block, basic_blocks)))
                return self.explicate_pred(test, thn, els, basic_blocks)
            case UnaryOp(_, operand):
                return self.explicate_effect(operand, cont, basic_blocks)
            case BinOp(left, _, right):
                cont = self.explicate_effect(right, cont, basic_blocks)
                return self.explicate_effect(left, cont, basic_blocks)
            case Compare(left, [_], [right]):
                cont = self.explicate_effect(right, cont, basic_blocks)
                return self.explicate_effect(left, cont, basic_blocks)
            case _:
                raise Exception('error in explicate_effect, unexpected ' + repr(e))

    def explicate_assign(
        self,
        rhs: expr,
        lhs: Name,
        cont: Code,
        basic_blocks: dict[str, list[stmt]],
    ) -> Code:
        match rhs:
            case Begin(stmts, result):
                cont = self.explicate_assign(result, lhs, cont, basic_blocks)
                return self.explicate_stmts(stmts, cont, basic_blocks)
            case IfExp(test, body, orelse):
                cont_block = create_block(cont, basic_blocks)
                thn = Promise(lambda: force(self.explicate_assign(body, lhs, cont_block, basic_blocks)))
                els = Promise(lambda: force(self.explicate_assign(orelse, lhs, cont_block, basic_blocks)))
                return self.explicate_pred(test, thn, els, basic_blocks)
            case _:
                return [Assign([lhs], rhs)] + force(cont)

    def explicate_pred(
        self,
        cnd: expr,
        thn: Code,
        els: Code,
        basic_blocks: dict[str, list[stmt]],
    ) -> Code:
        match cnd:
            case Begin(stmts, result):
                cont = self.explicate_pred(result, thn, els, basic_blocks)
                return self.explicate_stmts(stmts, cont, basic_blocks)
            case Compare(left, [op], [right]):
                return [If(cnd,
                           force(create_block(thn, basic_blocks)),
                           force(create_block(els, basic_blocks)))]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case UnaryOp(Not(), operand):
                return self.explicate_pred(operand, els, thn, basic_blocks)
            case IfExp(test, body, orelse):
                thn_block = create_block(thn, basic_blocks)
                els_block = create_block(els, basic_blocks)
                thn_code = Promise(lambda: force(self.explicate_pred(body, thn_block, els_block, basic_blocks)))
                els_code = Promise(lambda: force(self.explicate_pred(orelse, thn_block, els_block, basic_blocks)))
                return self.explicate_pred(test, thn_code, els_code, basic_blocks)
            case Name(_):
                comparison = Compare(cnd, [Eq()], [Constant(True)])
                return [If(comparison,
                           force(create_block(thn, basic_blocks)),
                           force(create_block(els, basic_blocks)))]
            case _:
                raise Exception('error in explicate_pred, unexpected ' + repr(cnd))

    def explicate_stmt(
        self, s: stmt, cont: Code, basic_blocks: dict[str, list[stmt]]
    ) -> Code:
        match s:
            case Expr(Call(Name('print'), [arg])):
                return [Expr(Call(Name('print'), [arg]))] + force(cont)
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                cont_block = create_block(cont, basic_blocks)
                thn = Promise(lambda: force(self.explicate_stmts(body, cont_block, basic_blocks)))
                els = Promise(lambda: force(self.explicate_stmts(orelse, cont_block, basic_blocks)))
                return self.explicate_pred(test, thn, els, basic_blocks)
            case _:
                raise Exception('error in explicate_stmt, unexpected ' + repr(s))

    def explicate_control(self, p: Module) -> CProgram:
        match p:
            case Module(body):
                new_body = [Return(Constant(0))]
                basic_blocks = {}
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                basic_blocks[label_name('start')] = force(new_body)
                return CProgram(basic_blocks)
            case _:
                raise Exception('error in explicate_control, unexpected ' + repr(p))

    ############################################################################
    # Select Instructions
    ############################################################################

    # The expression e passed to select_arg should furthermore be an atom.
    # (But there is no type for atoms, so the type of e is given as expr.)
    def select_arg(self, e: expr) -> arg:
        match e:
            case Constant(True):
                return Immediate(1)
            case Constant(False):
                return Immediate(0)
            case Constant(value):
                return Immediate(value)
            case Name(id):
                return Variable(id)
            case _:
                raise Exception('error in select_arg, unexpected ' + repr(e))

    def select_exp_into(self, e: expr) -> List[instr]:
        match e:
            case Call(Name('input_int'), []):
                return [Callq('read_int', 0)]
            case Constant(_) | Name(_):
                return []
            case UnaryOp(USub(), _) | UnaryOp(Not(), _):
                return []
            case BinOp(_, Add(), _) | BinOp(_, Sub(), _):
                return []
            case Compare(_, [_], [_]):
                return []
            case _:
                raise Exception('error in select_exp_into, unexpected ' + repr(e))

    def select_cc(self, op) -> str:
        match op:
            case Eq():
                return 'e'
            case NotEq():
                return 'ne'
            case Lt():
                return 'l'
            case LtE():
                return 'le'
            case Gt():
                return 'g'
            case GtE():
                return 'ge'
            case _:
                raise Exception('error in select_cc, unexpected ' + repr(op))

    def select_assign_into(self, lhs: Name | Reg, exp: expr) -> List[instr]:
        target = lhs if isinstance(lhs, Reg) else self.select_arg(lhs)
        match exp:
            case Constant(_) | Name(_):
                src = self.select_arg(exp)
                if src == target:
                    return []
                return [Instr('movq', [src, target])]
            case Call(Name('input_int'), []):
                if target == Reg('rax'):
                    return [Callq('read_int', 0)]
                return [
                    Callq('read_int', 0),
                    Instr('movq', [Reg('rax'), target]),
                ]
            case UnaryOp(USub(), atm):
                src = self.select_arg(atm)
                instrs = []
                if src != target:
                    instrs.append(Instr('movq', [src, target]))
                instrs.append(Instr('negq', [target]))
                return instrs
            case UnaryOp(Not(), atm):
                dst = target
                src = self.select_arg(atm)
                if src == dst:
                    return [Instr('xorq', [Immediate(1), dst])]
                else:
                    return [
                        Instr('movq', [src, dst]),
                        Instr('xorq', [Immediate(1), dst]),
                    ]
            case BinOp(left, Add(), right):
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
            case Compare(left, [op], [right]):
                left_arg = self.select_arg(left)
                right_arg = self.select_arg(right)
                cc = self.select_cc(op)
                return [
                    Instr('cmpq', [right_arg, left_arg]),
                    Instr('set' + cc, [ByteReg('al')]),
                    Instr('movzbq', [ByteReg('al'), target]),
                ]
            case _:
                raise Exception(
                    'error in select_assign_into, unexpected ' + repr(exp)
                )

    def select_tail(self, t: stmt) -> List[instr]:
        match t:
            case Return(value):
                return self.select_assign_into(Reg('rax'), value) + [
                    Jump('conclusion')
                ]
            case Goto(label):
                return [Jump(label)]
            case If(Compare(left, [op], [right]), [Goto(thn)], [Goto(els)]):
                cc = self.select_cc(op)
                left_arg = self.select_arg(left)
                right_arg = self.select_arg(right)
                return (
                    [
                        Instr('cmpq', [right_arg, left_arg]),
                        JumpIf(cc, thn),
                        Jump(els),
                    ]
                )
            case _:
                raise Exception('error in select_tail, unexpected ' + repr(t))

    def select_stmt(self, s: stmt) -> List[instr]:
        match s:
            case Expr(Call(Name('print'), [exp])):
                src = self.select_arg(exp)
                return [
                    Instr('movq', [src, Reg('rdi')]),
                    Callq('print_int', 1),
                ]
            case Expr(exp):
                return self.select_exp_into(exp)
            case Assign([lhs], exp):
                return self.select_assign_into(lhs, exp)
            case _:
                raise Exception('error in select_stmt, unexpected ' + repr(s))

    def select_instructions(self, p: CProgram) -> X86Program:
        match p:
            case CProgram(blocks):
                x86_blocks = {}
                for label, block in blocks.items():
                    if not block:
                        raise ValueError(f'empty CIf block {label}')
                    instructions = []
                    for stmt in block[:-1]:
                        instructions.extend(self.select_stmt(stmt))
                    instructions.extend(self.select_tail(block[-1]))
                    x86_blocks[label] = instructions
                return X86Program(x86_blocks)
            case _:
                raise Exception('error in select_instructions, unexpected ' + repr(p))

    ############################################################################
    # Assign Homes
    ############################################################################

    def build_control_flow_graph(self, blocks: dict[str, list[instr]]) -> DirectedAdjList:
        cfg = DirectedAdjList()
        # init vertex
        for label, block in blocks.items():
            cfg.add_vertex(label)

        def get_jump_blocks(label: str, instrs: list[instr]) -> list[str]:
            if not instrs:
                raise Exception('error in build_control_flow_graph, blocks is empty: ' + label)

            jump_blocks = []
            # the last two instructions
            for i in reversed(instrs[-2:]):
                if isinstance(i, Jump) or isinstance(i, JumpIf):
                    b = blocks.get(i.label, None)
                    if b == None and i.label != 'conclusion':
                        raise Exception('error in build_control_flow_graph blocks is not exist: ' + i.label)
                    jump_blocks.append(i.label)
            return jump_blocks

        for label, block in blocks.items():
            to_labels = get_jump_blocks(label, block)
            for b in to_labels:
                if cfg.has_edge(label, b):
                    continue
                cfg.add_edge(label, b)

        return cfg

    def operand_locations(self, l: arg) -> set[location]:
        match l:
            case Variable(id): return {l}
            case Reg(r): return {l}
            case Deref(reg, offset): return {Reg(reg)}
            case _ : return set()

    def written_locations(self, l: arg) -> set[location]:
        match l:
            case Variable(id): return {l}
            case Reg(r): return {l}
            case _ : return set()

    def address_base_locations(self, l: arg) -> set[location]:
        match l:
            case Deref(reg, _): return {Reg(reg)}
            case _ : return set()

    def R(self, i: instr) -> set[location]:
        match i:
            case Instr('cmpq', [src, dst]):
                return self.operand_locations(src) | self.operand_locations(dst)
            case Instr(iname, [src, dst]) if iname in ['addq', 'subq', 'xorq']:
                return self.operand_locations(src) | self.operand_locations(dst)
            case Instr(iname, [src, dst]) if iname in ['movq', 'movzbq']:
                return self.operand_locations(src) | self.address_base_locations(dst)
            case Instr('negq', [dst]):
                return self.operand_locations(dst)
            case Instr('pushq', [src]):
                return {Reg('rsp')} | self.operand_locations(src)
            case Instr('popq', [dst]):
                return {Reg('rsp')} | self.address_base_locations(dst)
            case Callq(_, n):
                passed = [Reg('rdi'), Reg('rsi'), Reg('rdx'), Reg('rcx'), Reg('r8'), Reg('r9')]
                return set(passed[:n])
            case Instr('retq', []):
                return {Reg('rax'), Reg('rsp')}
            case _:
                return set()

    def W(self, i: instr) -> set[location]:
        match i:
            case Instr(iname, [_, dst]) if iname in ['addq', 'subq', 'xorq']:
                return self.written_locations(dst)
            case Instr('movq', [_, dst]):
                return self.written_locations(dst)
            case Instr('movzbq', [_, dst]):
                return self.written_locations(dst)
            case Instr(iname, [dst]) if iname.startswith('set'):
                return self.written_locations(dst)
            case Instr('negq', [dst]):
                return self.written_locations(dst)
            case Instr('pushq', [dst]):
                return {Reg('rsp')}
            case Instr('popq', [dst]):
                return {Reg('rsp')} | self.written_locations(dst)
            case Callq(_, _):
                rs = [Reg('rax'), Reg('rcx'), Reg('rdx'), Reg('rsi'), Reg('rdi'), Reg('r8'), Reg('r9'), Reg('r10'), Reg('r11')]
                return set(rs)
            case Instr('retq', []):
                return {Reg('rsp')}
            case _:
                return set()

    # Liveness Analysis
    #
    # Lafter(k) = Lbefore(k + 1)
    # Lafter(last) = ∅ for a terminal block with no successors.
    # Lbefore(k) = (Lafter(k) − W(k)) ∪ R(k)
    # R(K): read instruction I(k)
    # W(K): write instruction I(k)
    #
    # Build the CFG and topologically sort its transpose so successor blocks
    # are analyzed before their predecessors. LIf CFGs are acyclic, so each
    # block can be analyzed once in this reverse topological order.
    # A Jump takes its target block's live-before set; a JumpIf unions that
    # set with the live set of the following instruction. After each scan,
    # save the first instruction's live-before set for that block. Stop when
    # no block-entry set changes; the final per-instruction live-after sets
    # are returned. The absent "conclusion" block has no live locations.
    #
    # Pseudocode:
    #   cfg = build_control_flow_graph(blocks)
    #   order = topological_sort(transpose(cfg))
    #   live_before_block = {label: ∅ for label in cfg}
    #   for each block B in order:
    #       live = ∅
    #       for each instruction i in reverse(B):
    #           if i is Jump(L):        live_after[i] = live_before_block[L]
    #           elif i is JumpIf(_, L): live_after[i] = live ∪ live_before_block[L]
    #           else:                   live_after[i] = live
    #           live = (live_after[i] − W(i)) ∪ R(i)
    #       live_before_block[B] = live
    def uncover_live(self, blocks: dict[str, list[instr]]) -> dict[instr, set[location]]:
        if not isinstance(blocks, dict):
            raise TypeError('uncover_live expects a dictionary of basic blocks')

        for label, instructions in blocks.items():
            if not instructions:
                raise ValueError(f'empty basic block: {label}')

        cfg = self.build_control_flow_graph(blocks)
        order = topological_sort(transpose(cfg))
        if len(order) != len(cfg.vertices()):
            raise ValueError('liveness analysis requires an acyclic control-flow graph')

        live_before_block = {label: set() for label in cfg.vertices()}
        live_after = {}
        for label in order:
            if label not in blocks:
                continue

            after_i = set()
            for i in reversed(blocks[label]):
                if isinstance(i, Jump):
                    if not cfg.has_edge(label, i.label):
                        raise ValueError(f'{i.label} is not a successor of block {label}')
                    after_i = live_before_block[i.label]
                elif isinstance(i, JumpIf):
                    if not cfg.has_edge(label, i.label):
                        raise ValueError(f'{i.label} is not a successor of block {label}')
                    after_i = after_i | live_before_block[i.label]
                live_after[i] = after_i
                after_i = after_i.difference(self.W(i)) | self.R(i)
            live_before_block[label] = after_i

        return live_after

    def all_home_vars(self, blocks: dict[str, list[instr]]) -> List[Variable]:
        home_vars = []
        seen = set()
        for instructions in blocks.values():
            for i in instructions:
                match i:
                    case Instr(_, args):
                        operands = args
                    case _:
                        operands = ()
                for operand in operands:
                    if isinstance(operand, Variable) and operand not in seen:
                        seen.add(operand)
                        home_vars.append(operand)
        return home_vars

    # build_interference
    # 1. If instruction Ik is a move instruction of the form movq s, d, then for every
    #    v ∈ Lafter(k), if v ̸= d and v ̸= s, add the edge (d, v).
    #    notice：d ∈ W(k) (Write), s is src(exlcude Deref, only include Reg and Variable)
    #    Compared with 2, src needs to be excluded, only this one difference.
    #
    # 2. For any other instruction Ik, for every d ∈ W(k) and every v∈ Lafter(k), if v ̸= d, add
    #    the edge (d, v).
    def build_interference(
        self,
        blocks: dict[str, list[instr]],
        live_after: dict[instr, set[location]],
    ) -> UndirectedAdjList:
        g = UndirectedAdjList()

        for vertex in self.all_home_vars(blocks):
            g.add_vertex(vertex)

        def add_edge(u, v):
            if not g.has_edge(u, v):
                g.add_edge(u, v)

        for i, lafter in live_after.items():
            w = self.W(i)
            match i:
                case Instr(iname, [src, _]) if iname in ['movq', 'movzbq']:
                    for d in w:
                        for v in lafter:
                            if v not in (src, d):
                                add_edge(d, v)
                case _:
                    for d in w:
                        for v in lafter:
                            if d != v:
                                add_edge(d, v)
        return g

    def move_related_graph(self, homes: List[Variable],
                           blocks: dict[str, list[instr]]) -> UndirectedAdjList:
        g = UndirectedAdjList()
        for variable in homes:
            g.add_vertex(variable)

        for instructions in blocks.values():
            for instruction in instructions:
                match instruction:
                    case Instr('movq', [Variable() as src, Variable() as dst]):
                        if src != dst and not g.has_edge(src, dst):
                            g.add_edge(src, dst)

        return g

    # Graph Coloring
    # saturation(u) = {c | ∃v.v∈ adjacent(u) and color(v) = c}
    # Algorithm: DSATUR
    # Input: A graph G
    # Output: An assignment color[v] for each vertex v ∈ G
    # 
    # W ←vertices(G)
    # while W ̸= ∅ do
    #   pick a vertex u from W with the highest saturation,
    #       breaking ties randomly
    #   find the lowest color c that is not in {color[v] : v ∈ adjacent(u)}
    #   color[u] ←c
    #   add color c to the saturation for the neighboring vertices
    #   W ←W − {u}

    #   Move Biasing
    #   build move related graph
    #   Among the candidate variables with the same saturation level,
    #   the ones that have a movement relationship with the already colored
    #   vertices and can use the color of that vertex are given priority.
    def allocate_registers(self, g: UndirectedAdjList,
                           move_graph: UndirectedAdjList,
                           p: X86Program) -> dict[Variable, arg]:
        w = [v for v in g.vertices() if isinstance(v, Variable)]
        p.used_callee = []
        if not w:
            return {}
        homes : dict[Variable, arg] = {}
        colors : dict[Variable, int] = {}
        saturations : dict[Variable, set[int]] = {}
        for v in w:
            saturations[v] = set()

        def available_move_colors(u: Variable) -> set[int]:
            return {
                colors[neighbor]
                for neighbor in move_graph.adjacent(u)
                if neighbor in colors and colors[neighbor] not in saturations[u]
            }

        def lowest_available_color(u: Variable) -> int:
            used_colors = saturations[u]
            color = 0
            while color in used_colors:
                color += 1
            return color

        def choose_vertex_and_color() -> Tuple[Variable, int]:
            max_saturation = max(len(saturations[v]) for v in w)
            candidates = [
                v for v in w if len(saturations[v]) == max_saturation
            ]

            for v in candidates:
                color = lowest_available_color(v)
                is_register_color = 0 <= color <= 10
                move_colors = {
                    c for c in available_move_colors(v)
                    if (0 <= c <= 10) == is_register_color
                }

                if move_colors:
                    return v, min(move_colors)

            u = candidates[0]
            return u, lowest_available_color(u)

        def color_to_location(c) -> arg:
            match c:
                case -5: return Reg('r15')
                case -4: return Reg('r11')
                case -3: return Reg('rbp')
                case -2: return Reg('rsp')
                case -1: return Reg('rax')

                case 0: return Reg('rcx')
                case 1: return Reg('rdx')
                case 2: return Reg('rsi')
                case 3: return Reg('rdi')
                case 4: return Reg('r8')
                case 5: return Reg('r9')
                case 6: return Reg('r10')
                case 7: return Reg('rbx')
                case 8: return Reg('r12')
                case 9: return Reg('r13')
                case 10: return Reg('r14')
                case n if n > 10:
                    return Deref('rbp', (n - 10) * -8)
                case _:
                    raise Exception('error in color_to_location, unexpected ' + repr(c))

        register_colors = {}
        for color in range(-5, 11):
            register_colors[color_to_location(color)] = color
        # select_instructions currently emits only %al (for setcc/movzbq);
        # add other byte registers here if the pass starts emitting them.
        register_colors[ByteReg('al')] = register_colors[Reg('rax')]

        def precolor_register_neighbors():
            for variable in w:
                for neighbor in g.adjacent(variable):
                    if isinstance(neighbor, Reg):
                        if neighbor not in register_colors:
                            raise ValueError(f'no register color defined for {neighbor}')
                        saturations[variable].add(register_colors[neighbor])

        precolor_register_neighbors()

        def add_saturation_to_neighbor(u, c):
            neighbors = g.adjacent(u)
            for n in neighbors:
                if isinstance(n, Variable):
                    saturations[n].add(c)

        while w:
            u, c = choose_vertex_and_color()
            colors[u] = c
            add_saturation_to_neighbor(u, c)
            w.remove(u)
            homes[u] = color_to_location(c)

        # set used_callee
        callee_saved = [
            Reg('rbx'), Reg('r12'), Reg('r13'), Reg('r14'), Reg('r15')
        ]
        for r in homes.values():
            if r in callee_saved:
                if r not in p.used_callee:
                    p.used_callee.append(r)

        # spill variable resize offset: add used_callee size
        spill_offset = len(p.used_callee) * 8
        for variable, home in homes.items():
            if isinstance(home, Deref) and home.reg == 'rbp' and home.offset < 0:
                homes[variable] = Deref('rbp', home.offset - spill_offset)
        return homes

    # %rsp must be 16-byte aligned before every call. The c callee-saved
    # registers are pushed after %rbp, occupying 8c bytes, and the spill
    # slots follow below them. The offsets in `homes` already include that
    # 8c area, so frame is the total number of bytes needed below %rbp;
    # stack_size is chosen so that 8c + stack_size is a multiple of 16.
    def compute_stack_size(self, homes: List[arg],
                           used_callee: List[Reg]) -> int:
        c = len(used_callee)
        frame = 8 * c
        for location in homes:
            if (isinstance(location, Deref)
                    and location.reg == 'rbp'
                    and location.offset < 0):
                frame = max(frame, -location.offset)
        stack_size = align(frame, 16) - 8 * c
        assert stack_size >= 0
        assert (stack_size + 8 * c) % 16 == 0
        assert stack_size + 8 * c >= frame
        return stack_size

    def assign_homes(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body) if isinstance(body, dict):
                homes = self.all_home_vars(body)
                live_after = self.uncover_live(body)

                interference = self.build_interference(body, live_after)
                move_graph = self.move_related_graph(homes, body)
                home = self.allocate_registers(interference, move_graph, p)

                def assign_arg(a: arg) -> arg:
                    if isinstance(a, Variable):
                        if a not in home:
                            raise KeyError(f'no home assigned to {a}')
                        return home[a]
                    return a

                def assign_instr(i: instr) -> instr:
                    match i:
                        case Instr(name, args):
                            return Instr(name, [assign_arg(a) for a in args])
                        case _:
                            return i

                for label, block in body.items():
                    body[label] = [assign_instr(i) for i in block]

                p.stack_size = self.compute_stack_size(
                    list(home.values()), p.used_callee)

                return p
            case _:
                raise Exception('error in assign_homes, unexpected ' + repr(p))

    ############################################################################
    # Remove Jumps
    #
    # Merge a basic block B into its unique predecessor P when P ends with
    # `Jump(B)`.  The trailing jump is redundant because control already falls
    # through from P into B's first instruction, so we delete the jump and
    # append B's instructions to P.
    ############################################################################

    def remove_jumps(self, p: X86Program) -> X86Program:
        """Merge a basic block into its unique predecessor.

        Pseudocode:

            edges = {}                       # block -> [(predecessor, kind)]
            for each block P in body:
                for instr in the last two instructions of P:
                    if instr is Jump(t):      edges[t].append((P, 'jmp'))
                    if instr is JumpIf(_, t): edges[t].append((P, 'jcc'))

            changed = True
            while changed:
                changed = False
                for each block B in body:
                    (P, kind) = the single incoming edge of B, or skip
                    if kind != 'jmp':         continue  # conditional: unsafe
                    if P == B:                continue  # self loop
                    if body[P][-1] != Jump(B): continue  # no fall through
                    body[P] = body[P][:-1] + body[B]
                    delete body[B]
                    changed = True
                    break
            return p
        """
        match p:
            case X86Program(body) if isinstance(body, dict):
                while True:
                    # Collect the incoming edges of every block so that we can
                    # identify the blocks that have a unique predecessor.
                    edges: dict[str, list[tuple[str, str]]] = {
                        label: [] for label in body}
                    for p_label, instrs in body.items():
                        for i in instrs[-2:]:
                            # Only edges to real blocks matter; `conclusion` is
                            # a dangling label at this stage of the pipeline.
                            if isinstance(i, Jump) and i.label in body:
                                edges[i.label].append((p_label, 'jmp'))
                            elif isinstance(i, JumpIf) and i.label in body:
                                edges[i.label].append((p_label, 'jcc'))

                    changed = False
                    for b_label in list(body.keys()):
                        incoming = edges[b_label]
                        # A block with zero or several predecessors is a join
                        # point (or unreachable), so it cannot be merged.
                        if len(incoming) != 1:
                            continue
                        p_label, kind = incoming[0]
                        # Merging a conditional jump would move the jump target
                        # and change which branch is taken, so skip it.
                        if kind != 'jmp':
                            continue
                        # A self loop cannot be inlined into itself.
                        if p_label == b_label:
                            continue
                        # The predecessor must end with `jmp B`; otherwise
                        # control would not fall through into B.
                        if not body[p_label]:
                            continue
                        last = body[p_label][-1]
                        if not (isinstance(last, Jump)
                                and last.label == b_label):
                            continue
                        body[p_label] = body[p_label][:-1] + body[b_label]
                        del body[b_label]
                        changed = True
                        # The edge map is stale after a merge; rebuild it.
                        break
                    if not changed:
                        break
                return p
            case _:
                raise Exception('error in remove_jumps, unexpected ' + repr(p))

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        MIN_INT32 = -(1<<31)
        MAX_INT32 = (1<<31)-1
        instrs = []
        match i:
            case Instr('movq', [src, dst]) if src == dst:
                return instrs
            case Instr('movq', [Deref() as src, Deref() as dst]) :
                instrs.append(Instr('movq', [src, Reg('rax')]))
                instrs.append(Instr('movq', [Reg('rax'), dst]))
            case Instr(iname, [Deref() as src, Deref() as dst]) if iname in ['addq', 'subq']:
                instrs.append(Instr('movq', [src, Reg('rax')]))
                instrs.append(Instr(iname, [Reg('rax'), dst]))
            case Instr('movq', [Immediate(n), dst]) if not (MIN_INT32 <= n <= MAX_INT32):
                instrs.append(Instr('movq', [Immediate(n), Reg('rax')]))
                instrs.append(Instr('movq', [Reg('rax'), dst]))
            case Instr('cmpq', [src, Immediate() as imm]):
                instrs.append(Instr('movq', [imm, Reg('rax')]))
                instrs.append(Instr('cmpq', [src, Reg('rax')]))
            case Instr('cmpq', [Deref() as src, Deref() as dst]):
                instrs.append(Instr('movq', [dst, Reg('rax')]))
                instrs.append(Instr('cmpq', [src, Reg('rax')]))
            case Instr('movzbq', [src, dst]) if not isinstance(dst, Reg):
                instrs.append(Instr('movzbq', [src, Reg('rax')]))
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
        used_callee = p.used_callee

        def prelude(stack_size) -> List[instr]:
            instrs = [
                Instr('pushq', [Reg('rbp')]),
                Instr('movq', [Reg('rsp'), Reg('rbp')]),
            ]
            instrs.extend(Instr('pushq', [reg]) for reg in used_callee)
            instrs.append(Instr('subq', [Immediate(stack_size), Reg('rsp')]))
            instrs.append(Jump('start'))
            return instrs

        def conclusion(stack_size) -> List[instr]:
            instrs = [Instr('addq', [Immediate(stack_size), Reg('rsp')])]
            instrs.extend(
                Instr('popq', [reg]) for reg in reversed(used_callee))
            instrs.extend([
                Instr('popq', [Reg('rbp')]),
                Instr('retq', []),
            ])
            return instrs

        match p:
            case X86Program(body) if isinstance(body, dict):
                if 'start' not in body:
                    raise ValueError(
                        "prelude_and_conclusion requires a 'start' block")
                main_instrs = prelude(p.stack_size)
                new_body = {'main': main_instrs, 'start': body['start']}
                body.pop('start')
                for label, block in body.items():
                    new_body[label] = block
                new_body['conclusion'] = conclusion(p.stack_size)
                p.body = new_body
                return p
            case _:
                raise Exception('error in prelude_and_conclusion, unexpected ' + repr(p))
