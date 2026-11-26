import ast
from ast import *
import typing
from utils import *
from x86_ast import *
import os
from graph import *
from dataflow_analysis import analyze_dataflow

Binding = typing.Tuple[Name, expr]
Temporaries = typing.List[Binding]

# The integer argument-passing registers, in order (section 8.2.1).
ARG_REGISTERS = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']


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
            case Tuple(es, Load()):
                return Tuple([self.shrink_exp(exp) for exp in es], Load())
            case List(es, Load()):
                return List([self.shrink_exp(exp) for exp in es], Load())
            case Subscript(exp, index, Load()):
                return Subscript(self.shrink_exp(exp), self.shrink_exp(index), Load())
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
            case Assign([Subscript(tup, index, Store())], value):
                return Assign([Subscript(self.shrink_exp(tup),
                                         self.shrink_exp(index), Store())],
                              self.shrink_exp(value))
            case If(exp, body, orelse):
                return If(self.shrink_exp(exp), [self.shrink_stmt(s) for s in body], [self.shrink_stmt(s) for s in orelse])
            case While(test, body, []):
                return While(self.shrink_exp(test), [self.shrink_stmt(s) for s in body], [])
            case Return(exp):
                return Return(self.shrink_exp(exp))
            case FunctionDef(name, params, bodys, dl, ty, comment):
                return FunctionDef(name, params, self.shrink_stmts(bodys), None, ty, None)
            case _:
                raise Exception('error in shrink_stmt, unexpected ' + repr(s))

    def shrink_stmts(self, ss: list[stmt]) -> list[stmt]:
        return [self.shrink_stmt(s) for s in ss]

    def shrink(self, p: Module) -> Module:
        match p:
            case Module(body):
                defs: list[stmt] = []
                stmts: list[stmt] = []
                for s in body:
                    if isinstance(s, FunctionDef):
                        defs.append(self.shrink_stmt(s))
                    else:
                        stmts.append(self.shrink_stmt(s))
                main = FunctionDef('main', [], stmts + [Return(Constant(0))],
                                   None, IntType(), None)
                defs.append(main)
                return Module(defs)
            case _:
                raise Exception('error in shrink, unexpected ' + repr(p))

    ############################################################################
    # Reveal Functions
    ############################################################################
    # A function name denotes an x86 label that must be turned into an address
    # with `leaq`, whereas a local variable lives in a register or on the
    # stack.  L_Fun conflates the two by representing both as Name, so this
    # pass distinguishes references to known functions:
    #
    #     Name(f)  =>  FunRef(f, n)          n = arity of f
    #
    # `env` maps every function visible at this point to its arity.  A local
    # binding shadows a function name, so parameters and assignment targets
    # are removed from `env` for the rest of the scope.  Keeping shadows as
    # Name prevents a later pass from compiling a local variable as a label.
    #
    # reveal_functions(Module(body)):
    #     env = { }
    #     for each FunctionDef(name, params, ...) in body:
    #         env[name] = number of parameters
    #     return Module([reveal_stmt(s, env) for s in body])
    ############################################################################

    def _param_names(self, params) -> list[str]:
        # The source-language type checker normalizes parameters into a list
        # of (name, type) pairs, but keep the raw ast.arguments form usable.
        if isinstance(params, ast.arguments):
            return [p.arg for p in params.args]
        return [p[0] for p in params]

    def reveal_exp(self, e: expr, env: dict[str, int]) -> expr:
        match e:
            case Name(id) if id in env:
                return FunRef(id, env[id])
            case Name(_) | Constant(_) | GlobalValue(_) | FunRef(_, _) | Allocate(_, _):
                return e
            case Call(func, args):
                return Call(self.reveal_exp(func, env),
                            [self.reveal_exp(a, env) for a in args])
            case UnaryOp(op, operand):
                return UnaryOp(op, self.reveal_exp(operand, env))
            case BinOp(left, op, right):
                return BinOp(self.reveal_exp(left, env), op,
                             self.reveal_exp(right, env))
            case Compare(left, ops, comparators):
                return Compare(self.reveal_exp(left, env), ops,
                               [self.reveal_exp(c, env) for c in comparators])
            case IfExp(test, body, orelse):
                return IfExp(self.reveal_exp(test, env),
                             self.reveal_exp(body, env),
                             self.reveal_exp(orelse, env))
            case Tuple(es, Load()):
                return Tuple([self.reveal_exp(x, env) for x in es], Load())
            case List(es, Load()):
                return List([self.reveal_exp(x, env) for x in es], Load())
            case Subscript(base, index, Load()):
                return Subscript(self.reveal_exp(base, env),
                                 self.reveal_exp(index, env), Load())
            case Begin(ss, result):
                return Begin(self.reveal_stmts(ss, env),
                             self.reveal_exp(result, env))
            case _:
                raise Exception('error in reveal_exp, unexpected ' + repr(e))

    def reveal_stmts(self, ss: list[stmt], env: dict[str, int]) -> list[stmt]:
        return [self.reveal_stmt(s, env) for s in ss]

    def reveal_stmt(self, s: stmt, env: dict[str, int]) -> stmt:
        match s:
            case FunctionDef():
                return self.reveal_def(s, env)
            case Return(value):
                return Return(self.reveal_exp(value, env))
            case Expr(value):
                return Expr(self.reveal_exp(value, env))
            case Assign([Name(id)], rhs):
                # Convert the right-hand side before shadowing the name so
                # that `f = inc` still turns inc into a FunRef.
                rhs2 = self.reveal_exp(rhs, env)
                env.pop(id, None)
                return Assign([Name(id)], rhs2)
            case Assign([Subscript(base, Constant(n), Store())], value):
                return Assign([Subscript(self.reveal_exp(base, env),
                                         Constant(n), Store())],
                              self.reveal_exp(value, env))
            case Assign([Subscript(base, index, Store())], value):
                return Assign([Subscript(self.reveal_exp(base, env),
                                         self.reveal_exp(index, env), Store())],
                              self.reveal_exp(value, env))
            case If(test, thn, els):
                return If(self.reveal_exp(test, env),
                          self.reveal_stmts(thn, env),
                          self.reveal_stmts(els, env))
            case While(test, body, []):
                return While(self.reveal_exp(test, env),
                             self.reveal_stmts(body, env), [])
            case _:
                raise Exception('error in reveal_stmt, unexpected ' + repr(s))

    def reveal_def(self, f: FunctionDef, env: dict[str, int]) -> FunctionDef:
        match f:
            case FunctionDef(name, params, body, dl, returns, comment):
                # A parameter shadows a function of the same name.
                new_env = dict(env)
                for p in self._param_names(params):
                    new_env.pop(p, None)
                return FunctionDef(name, params,
                                   self.reveal_stmts(body, new_env),
                                   dl, returns, comment)
            case _:
                raise Exception('error in reveal_def, unexpected ' + repr(f))

    # Name(f) -> FunRef(f, n)
    def reveal_functions(self, p: Module) -> Module:
        match p:
            case Module(body):
                env: dict[str, int] = {}
                for s in body:
                    match s:
                        case FunctionDef(name, params, b, dl, returns, comment):
                            env[name] = len(self._param_names(params))
                return Module([self.reveal_stmt(s, env) for s in body])
            case _:
                raise Exception('error in reveal_functions, unexpected ' + repr(p))

    ############################################################################
    #  Limit Functions
    ############################################################################
    #  The x86-64 calling convention passes at most six arguments in
    #  registers (rdi, rsi, rdx, rcx, r8, r9), so this pass rewrites
    #  functions and calls that involve more than six arguments: the first
    #  five arguments are passed as usual and the remaining ones are packed
    #  into a tuple that is passed as the sixth argument.  Keeping the
    #  number of parameters at six or fewer lets us pass every argument in
    #  registers and simplifies the implementation of tail calls.
    #
    #  pseudocode:
    #    limit_function_def(f):
    #        if len(f.params) <= 6:
    #            return f with body rewritten (no substitutions)
    #        tup = fresh name
    #        env = { x_i : (tup, i - 6) | i > 6 }
    #        params' = params[:5] + [(tup, TupleType([T_6, ..., T_n]))]
    #        return f with params' and body rewritten under env
    #
    #    limit_exp(e, env):
    #        Name(x) with x in env -> Subscript(Name(tup), Constant(k), Load())
    #        Call(f, es) -> Call(limit(f), es'[:5] + [Tuple(es'[5:])])
    #                       when there are more than six arguments
    #        otherwise recurse over the subexpressions
    #
    def limit_exp(self, e: expr,
                  env: dict[str, typing.Tuple[str, int]]) -> expr:
        match e:
            case Name(id) if id in env:
                (tup, index) = env[id]
                return Subscript(Name(tup), Constant(index), Load())
            case Call(func, args):
                new_func = self.limit_exp(func, env)
                new_args = [self.limit_exp(arg, env) for arg in args]
                # Pack arguments 6..n into a tuple so that the call site
                # passes at most six arguments.
                if len(new_args) > 6:
                    new_args = new_args[:5] + [Tuple(new_args[5:], Load())]
                return Call(new_func, new_args)
            case UnaryOp(op, operand):
                return UnaryOp(op, self.limit_exp(operand, env))
            case BinOp(left, op, right):
                return BinOp(self.limit_exp(left, env), op,
                             self.limit_exp(right, env))
            case Compare(left, ops, comparators):
                return Compare(self.limit_exp(left, env), ops,
                               [self.limit_exp(x, env) for x in comparators])
            case IfExp(test, body, orelse):
                return IfExp(self.limit_exp(test, env),
                             self.limit_exp(body, env),
                             self.limit_exp(orelse, env))
            case Tuple(elts, Load()):
                return Tuple([self.limit_exp(x, env) for x in elts], Load())
            case List(elts, Load()):
                return List([self.limit_exp(x, env) for x in elts], Load())
            case Subscript(base, index, Load()):
                return Subscript(self.limit_exp(base, env),
                                 self.limit_exp(index, env), Load())
            case Begin(stmts, result):
                return Begin(self.limit_stmts(stmts, env),
                             self.limit_exp(result, env))
            case Name(_) | Constant(_) | GlobalValue(_) | FunRef(_, _) \
               | Allocate(_, _) | AllocateArray(_, _):
                return e
            case _:
                raise Exception('error in limit_exp, unexpected ' + repr(e))

    def limit_stmts(self, ss: list[stmt],
                    env: dict[str, typing.Tuple[str, int]]) -> list[stmt]:
        return [self.limit_stmt(s, env) for s in ss]

    def limit_stmt(self, s: stmt,
                   env: dict[str, typing.Tuple[str, int]]) -> stmt:
        match s:
            case Expr(value):
                return Expr(self.limit_exp(value, env))
            case Return(value):
                return Return(self.limit_exp(value, env))
            case Assign([Name(id)], rhs) if id in env:
                # The parameter lives in the packed tuple now, so an
                # assignment must write through the tuple (Store context).
                (tup, index) = env[id]
                return Assign([Subscript(Name(tup), Constant(index), Store())],
                              self.limit_exp(rhs, env))
            case Assign([Name(id)], rhs):
                return Assign([Name(id)], self.limit_exp(rhs, env))
            case Assign([Subscript(base, index, Store())], value):
                return Assign([Subscript(self.limit_exp(base, env),
                                         self.limit_exp(index, env), Store())],
                              self.limit_exp(value, env))
            case If(test, thn, els):
                return If(self.limit_exp(test, env),
                          self.limit_stmts(thn, env),
                          self.limit_stmts(els, env))
            case While(test, body, []):
                return While(self.limit_exp(test, env),
                             self.limit_stmts(body, env), [])
            case _:
                raise Exception('error in limit_stmt, unexpected ' + repr(s))

    def limit_function_def(self, f: FunctionDef) -> FunctionDef:
        match f:
            case FunctionDef(name, params, bodys, dl, ty, comment):
                if isinstance(params, ast.arguments):
                    raise Exception('limit_function_def: function parameters '
                                    'must be normalized; run the type checker '
                                    'before limit_functions')
                if len(params) <= 6:
                    return FunctionDef(name, params,
                                       self.limit_stmts(bodys, {}),
                                       dl, ty, comment)
                # Pack parameters 6..n into a fresh tuple parameter and
                # substitute tuple reads/writes for those parameters.
                tup = generate_name('tup')
                env: dict[str, typing.Tuple[str, int]] = {}
                packed_types: list[Type] = []
                for (index, (x, t)) in enumerate(params[5:]):
                    env[x] = (tup, index)
                    packed_types.append(t)
                new_params = params[:5] + [(tup, TupleType(packed_types))]
                return FunctionDef(name, new_params,
                                   self.limit_stmts(bodys, env),
                                   dl, ty, comment)
            case _:
                raise Exception('error in limit_function_def, unexpected '
                                + repr(f))

    def limit_functions(self, p: Module) -> Module:
        match p:
            case Module(body):
                new_body: list[stmt] = []
                for s in body:
                    match s:
                        case FunctionDef():
                            new_body.append(self.limit_function_def(s))
                        case _:
                            new_body.append(self.limit_stmt(s, {}))
                return Module(new_body)
            case _:
                raise Exception('error in limit_functions, unexpected ' + repr(p))

    ############################################################################
    # Overload Resolution
    ############################################################################
    # The L_Array language overloads several operators:
    #
    #   A[i]      reads an element of an array when A has list type, and an
    #             element of a tuple when A has tuple type
    #   A[i] = v  writes an array element or a tuple element
    #   len(A)    computes the length of an array or of a tuple
    #
    # The L_Array type checker stores ListType(...) or TupleType(...) in the
    # has_type field of the expressions it checks, so this pass can resolve
    # every overload by inspecting has_type:
    #
    #   array load      ==>  array_load(A, i)
    #   array store     ==>  array_store(A, i, v)
    #   len(array)      ==>  array_len(A)
    #
    # Tuple operations are left unchanged.
    def resolve_exp(self, e: expr) -> expr:
        match e:
            case Subscript(base, index, Load()):
                base_ty = getattr(base, 'has_type', None)
                if base_ty is None:
                    raise ValueError('resolve: subscript base is missing has_type; '
                                     'run the type checker before resolve')
                base2 = self.resolve_exp(base)
                index2 = self.resolve_exp(index)
                if isinstance(base_ty, ListType):
                    return Call(Name('array_load'), [base2, index2])
                return Subscript(base2, index2, Load())
            case Call(Name('len'), [arg]):
                arg_ty = getattr(arg, 'has_type', None)
                if arg_ty is None:
                    raise ValueError('resolve: len argument is missing has_type; '
                                     'run the type checker before resolve')
                arg2 = self.resolve_exp(arg)
                if isinstance(arg_ty, ListType):
                    return Call(Name('array_len'), [arg2])
                return Call(Name('len'), [arg2])
            case UnaryOp(op, operand):
                return UnaryOp(op, self.resolve_exp(operand))
            case BinOp(left, op, right):
                return BinOp(self.resolve_exp(left), op, self.resolve_exp(right))
            case Compare(left, ops, comparators):
                return Compare(self.resolve_exp(left), ops,
                               [self.resolve_exp(c) for c in comparators])
            case IfExp(test, body, orelse):
                return IfExp(self.resolve_exp(test), self.resolve_exp(body),
                             self.resolve_exp(orelse))
            case Tuple(es, Load()):
                return Tuple([self.resolve_exp(x) for x in es], Load())
            case List(es, Load()):
                return List([self.resolve_exp(x) for x in es], Load())
            case Call(func, args):
                return Call(self.resolve_exp(func),
                            [self.resolve_exp(a) for a in args])
            case Begin(body, result):
                return Begin(self.resolve_stmts(body), self.resolve_exp(result))
            case Constant(_) | Name(_) | GlobalValue(_) | FunRef(_, _) \
                    | Allocate(_, _) | AllocateArray(_, _):
                return e
            case _:
                raise Exception('error in resolve_exp, unexpected ' + repr(e))

    def resolve_stmt(self, s: stmt) -> stmt:
        match s:
            case Assign([Subscript(base, index, Store())], value):
                base_ty = getattr(base, 'has_type', None)
                if isinstance(base_ty, ListType):
                    # An array element write becomes the array_store primitive.
                    return Expr(Call(Name('array_store'),
                                     [self.resolve_exp(base),
                                      self.resolve_exp(index),
                                      self.resolve_exp(value)]))
                return Assign([Subscript(self.resolve_exp(base),
                                         self.resolve_exp(index), Store())],
                              self.resolve_exp(value))
            case Expr(exp):
                return Expr(self.resolve_exp(exp))
            case Assign([Name(id)], exp):
                return Assign([Name(id)], self.resolve_exp(exp))
            case If(test, body, orelse):
                return If(self.resolve_exp(test), self.resolve_stmts(body),
                          self.resolve_stmts(orelse))
            case While(test, body, []):
                return While(self.resolve_exp(test), self.resolve_stmts(body), [])
            case Return(value):
                # Functions may return array accesses, e.g. return A[i].
                return Return(self.resolve_exp(value))
            case FunctionDef(name, params, bodys, dl, ty, comment):
                # Resolve the overloaded operations inside every function body.
                return FunctionDef(name, params, self.resolve_stmts(bodys),
                                   dl, ty, comment)
            case _:
                raise Exception('error in resolve_stmt, unexpected ' + repr(s))

    def resolve_stmts(self, ss: list[stmt]) -> list[stmt]:
        return [self.resolve_stmt(s) for s in ss]

    def resolve(self, p: Module) -> Module:
        match p:
            case Module(body):
                return Module(self.resolve_stmts(body))
            case _:
                raise Exception('error in resolve, unexpected ' + repr(p))

    ############################################################################
    # Check Bounds
    ############################################################################
    # An array access can be out of bounds at run time, whereas the reference
    # interpreter signals TrappedError.  The compiled program must therefore
    # check the index before each access and halt on failure.  For
    #
    #   array_load(A, i)          and          array_store(A, i, v)
    #
    # this pass generates
    #
    #   begin:
    #     t.0 = A
    #     t.1 = i
    #     t.2 = array_len(t.0)
    #     if t.1 >= 0:                          # the index must not be negative
    #       if t.1 < t.2:                       # and it must be in range
    #         array_load(t.0, t.1)              # or array_store(t.0, t.1, v)
    #       else: exit()
    #     else: exit()
    #   end
    #
    # Binding A, i, and the length to temporaries makes sure that every
    # subexpression is evaluated exactly once.  The value of an array_store
    # stays inside the in-bounds branch, matching the interpreter: an
    # out-of-bounds store never evaluates the stored expression.
    def bounds_checked(self, arr: expr, index: expr,
                       access: typing.Callable[[Name, Name], expr]) -> expr:
        t_arr = Name(generate_name('tmp'))
        t_idx = Name(generate_name('tmp'))
        t_len = Name(generate_name('tmp'))
        check_lower = Compare(t_idx, [GtE()], [Constant(0)])
        check_upper = Compare(t_idx, [Lt()], [t_len])
        exit_call = Call(Name('exit'), [])
        return Begin(
            [Assign([t_arr], self.check_bounds_exp(arr)),
             Assign([t_idx], self.check_bounds_exp(index)),
             Assign([t_len], Call(Name('array_len'), [t_arr]))],
            IfExp(check_lower,
                  IfExp(check_upper, access(t_arr, t_idx), exit_call),
                  exit_call))

    def check_bounds_exp(self, e: expr) -> expr:
        match e:
            case Call(Name('array_load'), [arr, index]):
                return self.bounds_checked(
                    arr, index,
                    lambda a, i: Call(Name('array_load'), [a, i]))
            case Call(Name('array_store'), [arr, index, value]):
                return self.bounds_checked(
                    arr, index,
                    lambda a, i: Call(Name('array_store'),
                                      [a, i, self.check_bounds_exp(value)]))
            case UnaryOp(op, operand):
                return UnaryOp(op, self.check_bounds_exp(operand))
            case BinOp(left, op, right):
                return BinOp(self.check_bounds_exp(left), op,
                             self.check_bounds_exp(right))
            case Compare(left, ops, comparators):
                return Compare(self.check_bounds_exp(left), ops,
                               [self.check_bounds_exp(c) for c in comparators])
            case IfExp(test, body, orelse):
                return IfExp(self.check_bounds_exp(test),
                             self.check_bounds_exp(body),
                             self.check_bounds_exp(orelse))
            case Tuple(es, Load()):
                return Tuple([self.check_bounds_exp(x) for x in es], Load())
            case List(es, Load()):
                return List([self.check_bounds_exp(x) for x in es], Load())
            case Call(func, args):
                return Call(self.check_bounds_exp(func),
                            [self.check_bounds_exp(a) for a in args])
            case Begin(body, result):
                return Begin(self.check_bounds_stmts(body),
                             self.check_bounds_exp(result))
            case Subscript(base, Constant(index), Load()):
                return Subscript(self.check_bounds_exp(base), Constant(index),
                                 Load())
            case Constant(_) | Name(_) | GlobalValue(_) | FunRef(_, _) \
                    | Allocate(_, _) | AllocateArray(_, _):
                return e
            case _:
                raise Exception('error in check_bounds_exp, unexpected '
                                + repr(e))

    def check_bounds_stmt(self, s: stmt) -> stmt:
        match s:
            case Expr(exp):
                return Expr(self.check_bounds_exp(exp))
            case Assign([Name(id)], exp):
                return Assign([Name(id)], self.check_bounds_exp(exp))
            case Assign([Subscript(tup, Constant(n), Store())], value):
                return Assign([Subscript(self.check_bounds_exp(tup),
                                         Constant(n), Store())],
                              self.check_bounds_exp(value))
            case If(test, body, orelse):
                return If(self.check_bounds_exp(test),
                          self.check_bounds_stmts(body),
                          self.check_bounds_stmts(orelse))
            case While(test, body, []):
                return While(self.check_bounds_exp(test),
                             self.check_bounds_stmts(body), [])
            case Return(value):
                # Functions may return array accesses, e.g. return A[i].
                return Return(self.check_bounds_exp(value))
            case FunctionDef(name, params, bodys, dl, ty, comment):
                # Insert bounds checks inside every function body.
                return FunctionDef(name, params, self.check_bounds_stmts(bodys),
                                   dl, ty, comment)
            case _:
                raise Exception('error in check_bounds_stmt, unexpected '
                                + repr(s))

    def check_bounds_stmts(self, ss: list[stmt]) -> list[stmt]:
        return [self.check_bounds_stmt(s) for s in ss]

    def check_bounds(self, p: Module) -> Module:
        match p:
            case Module(body):
                return Module(self.check_bounds_stmts(body))
            case _:
                raise Exception('error in check_bounds, unexpected ' + repr(p))

    ############################################################################
    # Expose Allocation
    ############################################################################
    # Lower tuple creation into the explicit allocation protocol of L_Alloc:
    #
    #   (e0, ..., e_{n-1})  ==>  begin
    #                              init.0 = e0
    #                              ...
    #                              init.n-1 = e_{n-1}
    #                              if global_value(free_ptr) + bytes < global_value(fromspace_end):
    #                              else:
    #                                  collect(bytes)
    #                              alloc.k = allocate(n, tuple_type)
    #                              alloc.k[0] = init.0
    #                              ...
    #                              alloc.k[n-1] = init.n-1
    #                              alloc.k
    #                            end
    #
    # where bytes = 8 * (n + 1): eight bytes for the tuple's tag plus eight
    # bytes per element.  The initializers are evaluated (into temporaries)
    # before the allocation because a tuple may trigger the garbage collector,
    # and the collector must never observe an allocated but uninitialized tuple.
    def expose_alloc_exp(self, e: expr) -> expr:
        match  e:
            case UnaryOp(op, operand):
                return UnaryOp(op, self.expose_alloc_exp(operand))
            case BinOp(left, op, right):
                return BinOp(self.expose_alloc_exp(left), op, self.expose_alloc_exp(right))
            case Compare(left, ops, comparators):
                return Compare(self.expose_alloc_exp(left), ops,
                               [self.expose_alloc_exp(comparator) for comparator in comparators])
            case IfExp(test, body, orelse):
                return IfExp(self.expose_alloc_exp(test), self.expose_alloc_exp(body),
                             self.expose_alloc_exp(orelse))
            case Call(func, args):
                return Call(self.expose_alloc_exp(func),
                            [self.expose_alloc_exp(arg) for arg in args])
            case Begin(body, result):
                return Begin(self.expose_alloc_stmts(body), self.expose_alloc_exp(result))
            case List(es, Load()):
                # Array creation (section 7.9.4): like a tuple, the
                # initializers are evaluated first, then space is reserved,
                # and finally the elements are stored.  The differences are
                # that the allocation uses AllocateArray (an uninitialized
                # array) and that its type is the ListType(...) recorded in
                # has_type by the type checker.
                if not hasattr(e, 'has_type'):
                    raise ValueError('expose_alloc_exp: array is missing has_type; '
                                     'run the type checker before expose_allocation')
                init_names = []
                stmts: list[stmt] = []
                for init in es:
                    name = generate_name('init')
                    init_names.append(name)
                    stmts.append(Assign([Name(name)], self.expose_alloc_exp(init)))
                bytes = 8 * (len(es) + 1)
                cond = Compare(BinOp(GlobalValue('free_ptr'), Add(), Constant(bytes)),
                               [Lt()], [GlobalValue('fromspace_end')])
                stmts.append(If(cond, [], [Collect(bytes)]))
                alloc = generate_name('alloc')
                stmts.append(Assign([Name(alloc)],
                                    AllocateArray(len(es), e.has_type)))
                for index, name in enumerate(init_names):
                    stmts.append(Assign([Subscript(Name(alloc), Constant(index),
                                                   Store())],
                                        Name(name)))
                return Begin(stmts, Name(alloc))
            case Tuple(es, Load()):
                if not hasattr(e, 'has_type'):
                    raise ValueError('expose_alloc_exp: tuple is missing has_type; '
                                     'run the type checker before expose_allocation')
                # 1. Evaluate the initializers left to right into temporaries.
                init_names = []
                stmts: list[stmt] = []
                for init in es:
                    name = generate_name('init')
                    init_names.append(name)
                    stmts.append(Assign([Name(name)], self.expose_alloc_exp(init)))
                # 2. Collect only when there is not enough room in the from-space.
                bytes = 8 * (len(es) + 1)
                cond = Compare(BinOp(GlobalValue('free_ptr'), Add(), Constant(bytes)),
                               [Lt()], [GlobalValue('fromspace_end')])
                stmts.append(If(cond, [], [Collect(bytes)]))
                # 3. Allocate the tuple and initialize its elements.
                alloc = generate_name('alloc')
                stmts.append(Assign([Name(alloc)], Allocate(len(es), e.has_type)))
                for index, name in enumerate(init_names):
                    stmts.append(Assign([Subscript(Name(alloc), Constant(index), Store())],
                                        Name(name)))
                return Begin(stmts, Name(alloc))
            case Subscript(exp, Constant(index), Load()):
                return Subscript(self.expose_alloc_exp(exp), Constant(index), Load())
            case Constant(_) | Name(_) | GlobalValue(_) | FunRef(_, _) \
                    | Allocate(_, _):
                # FunRef is an atom here: section 8.6 turns it into a
                # temporary assignment, and select_instructions compiles that
                # assignment into a leaq.
                return e
            case _:
                raise Exception('error in expose_alloc_exp, unexpected ' + repr(e))

    def expose_alloc_stmts(self, ss: list[stmt]) -> list[stmt]:
        return [self.expose_alloc_stmt(s) for s in ss]

    def expose_alloc_stmt(self, s: stmt) -> stmt:
        match s:
            case Expr(exp):
                return Expr(self.expose_alloc_exp(exp))
            case Assign([Name(id)], exp):
                return Assign([Name(id)], self.expose_alloc_exp(exp))
            case Assign([Subscript(tup, Constant(index), Store())], value):
                return Assign([Subscript(self.expose_alloc_exp(tup),
                                         Constant(index), Store())],
                              self.expose_alloc_exp(value))
            case If(test, body, orelse):
                return If(self.expose_alloc_exp(test),
                          self.expose_alloc_stmts(body),
                          self.expose_alloc_stmts(orelse))
            case While(test, body, []):
                return While(self.expose_alloc_exp(test),
                             self.expose_alloc_stmts(body), [])
            case Return(value):
                return Return(self.expose_alloc_exp(value))
            case Collect(size):
                return Collect(size)
            case _:
                raise Exception('error in expose_alloc_stmt, unexpected ' + repr(s))

    def expose_allocation(self, p: Module) -> Module:
        match p:
            case Module(body):
                # Function definitions keep their shape; only their bodies
                # contain tuples that need to be lowered.
                new_body: list[stmt] = []
                for stmt in body:
                    match stmt:
                        case FunctionDef(name, params, bodys, dl, ty, comment):
                            new_body.append(FunctionDef(
                                name, params, self.expose_alloc_stmts(bodys),
                                dl, ty, comment))
                        case _:
                            new_body.append(self.expose_alloc_stmt(stmt))
                return Module(new_body)
            case _:
                raise Exception('error in expose_allocation, unexpected ' + repr(p))

    ############################################################################
    # Remove Complex Operands
    ############################################################################
    # Section 8.6: the new decisions for L_Fun are how to classify FunRef and
    # Call.
    #
    #   FunRef(f, n)        ==>  tmp = FunRef(f, n)        when an atom is needed
    #   Call(callee, args)  ==>  tmp = Call(callee, args)  when an atom is needed
    #
    # A call expands to a sequence of instructions, so it cannot be an
    # immediate operand of an x86 instruction; the callee and the arguments of
    # a call must be atoms.  A function reference must be turned into an
    # address with leaq, which needs a register as its target, so it is also
    # complex.  A Call that is the value of a Return or the right-hand side of
    # an assignment stays as is, so that explicate_control can recognize tail
    # calls.
    #
    # The output language L_mon_FunRef is Module([def..., stmt...]): every
    # function definition is processed like the body of main.

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
            case GlobalValue(var) as g:
                return (g, [])
            case FunRef(id, arity) as fref:
                # A function reference is complex: select_instructions
                # compiles it into a leaq, which needs a register as its
                # target, so an atom position binds it to a temporary.
                return finish_rco(fref, [])
            case Call(Name('input_int'), []) as call:
                return finish_rco(call, [])
            case Call(Name('len'), [exp]):
                (arg, bindings) = self.rco_exp(exp, True)
                call = Call(Name('len'), [arg])
                return finish_rco(call, bindings)
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
            case Allocate(n, t) as alloc:
                return finish_rco(alloc, [])
            case Subscript(exp, Constant(n), Load()):
                (tup_name, tup_bindings) = self.rco_exp(exp, True)
                r = Subscript(tup_name, Constant(n), Load())
                return finish_rco(r, tup_bindings)
            case AllocateArray(n, t) as alloc:
                # An array allocation is a complex operand, but its length
                # and type are constants, so there is nothing to reduce.
                return finish_rco(alloc, [])
            case Call(Name('array_len'), [exp]):
                (arg, bindings) = self.rco_exp(exp, True)
                return finish_rco(Call(Name('array_len'), [arg]), bindings)
            case Call(Name('array_load'), [arr, index]):
                (arr_name, arr_bindings) = self.rco_exp(arr, True)
                (index_name, index_bindings) = self.rco_exp(index, True)
                return finish_rco(Call(Name('array_load'), [arr_name, index_name]),
                                  arr_bindings + index_bindings)
            case Call(Name('array_store'), [arr, index, value]):
                (arr_name, arr_bindings) = self.rco_exp(arr, True)
                (index_name, index_bindings) = self.rco_exp(index, True)
                (value_name, value_bindings) = self.rco_exp(value, True)
                return finish_rco(
                    Call(Name('array_store'), [arr_name, index_name, value_name]),
                    arr_bindings + index_bindings + value_bindings)
            case Call(Name('exit'), []) as call:
                return finish_rco(call, [])
            case Call(func, args):
                # A call is a complex operand: it expands to a sequence of
                # instructions, so an atom position binds it to a temporary.
                # The callee and every argument must be atoms; a FunRef callee
                # therefore becomes a temporary holding the function address.
                (func_expr, bindings) = self.rco_exp(func, True)
                reduced_args = []
                for arg in args:
                    (arg_expr, arg_bindings) = self.rco_exp(arg, True)
                    reduced_args.append(arg_expr)
                    bindings += arg_bindings
                return finish_rco(Call(func_expr, reduced_args), bindings)
            case Begin(ss, result_exp):
                # Remove complex operands from the begin's statements and
                # from its result expression.  The result's temporaries must
                # be run *inside* the begin, after the statements, because
                # the statements have side effects (collect, tuple stores)
                # that must happen before the result is computed.
                body: List[stmt] = []
                for s in ss:
                    body.extend(self.rco_stmt(s))
                (r, bs) = self.rco_exp(result_exp, need_atomic)
                if need_atomic:
                    if not body:
                        return (r, bs)
                    body += make_assigns(bs)
                    tmp = Name(generate_name('tmp'))
                    return (tmp, [(tmp, Begin(body, r))])
                body += make_assigns(bs)
                return (Begin(body, r), [])
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
            case While(test, body, []):
                (test_expr, test_bindings) = self.rco_exp(test, False)
                body_stmts = []
                for stmt in body:
                    body_stmts.extend(self.rco_stmt(stmt))
                # Recompute the condition's temporary assignments at the end
                # of each iteration so that the next test sees fresh values.
                stmts = make_assigns(test_bindings)
                body_stmts += make_assigns(test_bindings)
                stmts.append(While(test_expr, body_stmts, []))
                return stmts
            case Assign([Subscript(tup, Constant(n), Store())], value):
                # The tuple expression is evaluated before the right-hand
                # side, and both must be atomic in the output language.
                (tup_expr, tup_bindings) = self.rco_exp(tup, True)
                (value_expr, value_bindings) = self.rco_exp(value, True)
                stmts = make_assigns(tup_bindings)
                stmts += make_assigns(value_bindings)
                stmts.append(Assign([Subscript(tup_expr, Constant(n), Store())], value_expr))
                return stmts
            case Return(value):
                # The result of a tail call stays a Call, so that
                # explicate_control can turn it into a TailCall.
                (expr, temporaries) = self.rco_exp(value, False)
                stmts = make_assigns(temporaries)
                stmts.append(Return(expr))
                return stmts
            case Collect(n):
                return [Collect(n)]
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(s))

    def rco_stmts(self, ss: list[stmt]) -> list[stmt]:
        stmts: list[stmt] = []
        for s in ss:
            stmts += self.rco_stmt(s)
        return stmts

    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(body):
                new_body: list[stmt] = []
                for stmt in body:
                    match stmt:
                        case FunctionDef(name, params, bodys, dl, ty, comment):
                            new_body.append(FunctionDef(
                                name, params, self.rco_stmts(bodys),
                                dl, ty, comment))
                        case _:
                            new_body += self.rco_stmt(stmt)
                return Module(new_body)
            case _:
                raise Exception('error in remove_complex_operands, unexpected ' + repr(p))

    ############################################################################
    # Explicate Control
    ############################################################################
    # The input is L_mon_FunRef: a module whose body is a list of function
    # definitions (shrink has already turned the top-level statements into
    # main), and whose expressions are in monadic normal form.
    #
    # The output is C_Fun:
    #
    #   tail  ::= Return(exp) | Goto(label)
    #           | If(Compare(atm, [cmp], atm), [Goto(label)], [Goto(label)])
    #           | TailCall(atm, atm*)
    #   block ::= label: stmt* tail
    #   def   ::= FunctionDef(label, params, {block, ...}, None, type, None)
    #   C_Fun ::= CProgramDefs([def, ...])
    #
    # Every function definition gets its own dictionary of basic blocks.  The
    # entry block is named <function>_start, which is the convention used by
    # the C_Fun interpreter.
    #
    # The interesting part of the pass is the position of an expression:
    #
    #   tail position      a call becomes TailCall, so that the x86 backend
    #                      can jump to the callee instead of calling it
    #   predicate position a Call is evaluated and compared with True
    #                      (a FunRef can never be a Boolean)
    #   effect position    a Call is kept because it may have side effects
    #   assignment         a Call can stay on the right-hand side
    #
    # Pseudocode for one function definition:
    #
    #   def explicate_def(name, params, body):
    #       blocks = {}
    #       blocks[name + '_start'] = force(explicate_stmts(body, [], blocks))
    #       return FunctionDef(name, params, blocks, None, type, None)
    #

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
            case Constant(_) | Name(_) | GlobalValue(_) | FunRef(_, _):
                # Atoms have no side effects, so the effect context drops them.
                return cont
            case Call(Name('input_int'), []) as call:
                return [Expr(call)] + force(cont)
            case Allocate(_, _) as alloc:
                # Allocation mutates the heap, so keep it in effect position.
                return [Expr(alloc)] + force(cont)
            case AllocateArray(_, _) as alloc:
                # Array allocation mutates the heap as well.
                return [Expr(alloc)] + force(cont)
            case Call(Name('array_store'), [_, _, _]) as store:
                # An array store writes to the heap.
                return [Expr(store)] + force(cont)
            case Call(Name('exit'), []) as call:
                # exit never returns, so the continuation is unreachable;
                # it is still kept so that the block has a valid tail.
                return [Expr(call)] + force(cont)
            case Subscript(_, _, Load()) | Call(Name('len'), [_]) \
                    | Call(Name('array_len'), [_]) \
                    | Call(Name('array_load'), [_, _]):
                # Tuple/array access and len are pure; their operands are atoms.
                return cont
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
            case Call(_, _) as call:
                # A call may have side effects, so it stays in effect position.
                return [Expr(call)] + force(cont)
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
            case Call(_, _) as call:
                # A call may return a Boolean, so evaluate it into a temporary
                # and compare the result with True.  (A FunRef cannot be a
                # Boolean, so there is deliberately no FunRef case.)
                tmp = Name(generate_name('tmp'))
                comparison = Compare(tmp, [Eq()], [Constant(True)])
                return [Assign([tmp], call)] + \
                       [If(comparison,
                           force(create_block(thn, basic_blocks)),
                           force(create_block(els, basic_blocks)))]
            case _:
                raise Exception('error in explicate_pred, unexpected ' + repr(cnd))

    def explicate_tail(
        self, e: expr, basic_blocks: dict[str, list[stmt]]
    ) -> Code:
        # Expressions in tail position produce a block tail.  The default is
        # Return; a call in tail position becomes TailCall so that the backend
        # can jump to the callee instead of using callq + retq.
        match e:
            case Begin(stmts, result):
                cont = self.explicate_tail(result, basic_blocks)
                return self.explicate_stmts(stmts, cont, basic_blocks)
            case IfExp(test, body, orelse):
                thn = Promise(lambda: force(self.explicate_tail(body, basic_blocks)))
                els = Promise(lambda: force(self.explicate_tail(orelse, basic_blocks)))
                return self.explicate_pred(test, thn, els, basic_blocks)
            case Call(func, args):
                return [TailCall(func, args)]
            case _:
                return [Return(e)]

    def explicate_stmt(
        self, s: stmt, cont: Code, basic_blocks: dict[str, list[stmt]]
    ) -> Code:
        match s:
            case Expr(Call(Name('print'), [arg])):
                return [Expr(Call(Name('print'), [arg]))] + force(cont)
            case Assign([Subscript(tup, Constant(n), Store())], value):
                # Tuple element store: a single C_Tup statement.  RCO
                # guarantees that both the tuple expression and the value
                # are atomic, so no further explication is needed.
                return [s] + force(cont)
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                cont_block = create_block(cont, basic_blocks)
                thn = Promise(lambda: force(self.explicate_stmts(body, cont_block, basic_blocks)))
                els = Promise(lambda: force(self.explicate_stmts(orelse, cont_block, basic_blocks)))
                return self.explicate_pred(test, thn, els, basic_blocks)
            case While(test, body, []):
                # A while loop is explicated as:
                #   loop_head:  if test: goto body_block else: goto cont
                #   body_block: body; goto loop_head
                # The condition is explicated with explicate_pred so that
                # complex tests are evaluated before every iteration.
                loop_head = label_name(generate_name('loop_head'))
                cont_block = create_block(cont, basic_blocks)
                body_stmts = self.explicate_stmts(body, [Goto(loop_head)], basic_blocks)
                basic_blocks[loop_head] = force(
                    self.explicate_pred(test, body_stmts, cont_block, basic_blocks))
                return [Goto(loop_head)]
            case Collect(n): 
                return [Collect(n)] + force(cont)
            case Return(value):
                # A return is terminal, so the surrounding continuation is
                # discarded and the value is explicated in tail position.
                return self.explicate_tail(value, basic_blocks)
            case _:
                raise Exception('error in explicate_stmt, unexpected ' + repr(s))

    def explicate_def(self, f: FunctionDef) -> FunctionDef:
        # Each function definition gets its own dictionary of basic blocks.
        # The initial continuation is empty: a function body normally ends in
        # Return, which discards the continuation.  Unreachable continuations
        # are never forced, so they do not create empty blocks.
        match f:
            case FunctionDef(name, params, bodys, dl, ty, comment):
                basic_blocks: dict[str, list[stmt]] = {}
                entry = name + '_start'
                basic_blocks[entry] = force(
                    self.explicate_stmts(bodys, [], basic_blocks))
                return FunctionDef(name, params, basic_blocks, dl, ty, comment)
            case _:
                raise Exception('error in explicate_def, unexpected ' + repr(f))

    def explicate_control(self, p: Module) -> CProgramDefs:
        match p:
            case Module(body):
                defs: list[FunctionDef] = []
                for s in body:
                    match s:
                        case FunctionDef() as f:
                            defs.append(self.explicate_def(f))
                        case _:
                            raise Exception('error in explicate_control, '
                                            'unexpected ' + repr(s))
                return CProgramDefs(defs)
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
            case GlobalValue(var):
                return Global(var)
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
            case GlobalValue(_) | Subscript(_, _, Load()) | Call(Name('len'), [_]) \
                    | Call(Name('array_len'), [_]) \
                    | Call(Name('array_load'), [_, _]):
                # These expressions are pure, so they have no effect when
                # used as a statement.
                return []
            case Allocate(_, _) as alloc:
                return self.select_assign_into(Reg('rax'), alloc)
            case AllocateArray(_, _) as alloc:
                return self.select_assign_into(Reg('rax'), alloc)
            case Call(Name('array_store'), [_, _, _]) as store:
                return self.select_assign_into(Reg('rax'), store)
            case Call(Name('exit'), []) as call:
                return self.select_assign_into(Reg('rax'), call)
            case Call(_, _) as call:
                # A call of a user-defined function may have side effects.
                return self.select_assign_into(Reg('rax'), call)
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
            case Is():
                # Comparing two tuple pointers with `is` is an equality
                # comparison on the addresses.
                return 'e'
            case _:
                raise Exception('error in select_cc, unexpected ' + repr(op))

    def tuple_tag(self, ty: Type) -> int:
        # The tag of a tuple (see section 7.2.3) has the following layout:
        #   bit 0     : set to 1 when the tuple has not been copied yet
        #   bits 1-6  : the length of the tuple
        #   bits 7-56 : a pointer mask, one bit per element, set to 1 when
        #               the element is (or may be) a tuple pointer
        if not isinstance(ty, TupleType):
            raise ValueError('tuple_tag: expected a TupleType, got ' + repr(ty))
        types = ty.types
        if len(types) > 50:
            raise ValueError('tuple_tag: tuples may have at most 50 elements')
        mask = 0
        for (i, t) in enumerate(types):
            if isinstance(t, TupleType):
                mask = mask | (1 << i)
        return (mask << 7) | (len(types) << 1) | 1

    def array_tag(self, ty: Type, length: int) -> int:
        # The tag of an array (see section 7.9.1) has the following layout:
        #   bit 0     : set to 1 when the array has not been copied yet
        #   bit 1     : pointer mask, 1 when every element is a heap pointer
        #   bits 2-61 : the length of the array (60 bits)
        #   bit 62    : 0 for a tuple, 1 for an array
        if not isinstance(ty, ListType):
            raise ValueError('array_tag: expected a ListType, got ' + repr(ty))
        pointer_mask = 1 if isinstance(ty.elt_type, (ListType, TupleType)) else 0
        return 1 | (pointer_mask << 1) | (length << 2) | (1 << 62)

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
            case Call(Name('len'), [arg]):
                # The length is stored in bits 1-6 of the tuple's tag.
                src = self.select_arg(arg)
                instrs = []
                if src != Reg('r11'):
                    instrs.append(Instr('movq', [src, Reg('r11')]))
                instrs.extend([
                    Instr('movq', [Deref('r11', 0), target]),
                    Instr('andq', [Immediate(126), target]),
                    Instr('sarq', [Immediate(1), target]),
                ])
                return instrs
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
            case Subscript(tup, Constant(n), Load()):
                # Skip the 8-byte tag, then read the n-th element.
                tup_arg = self.select_arg(tup)
                instrs = []
                if tup_arg != Reg('r11'):
                    instrs.append(Instr('movq', [tup_arg, Reg('r11')]))
                instrs.append(Instr('movq', [Deref('r11', 8 * (n + 1)), target]))
                return instrs
            case Allocate(n, ty):
                # Inline allocation: bump free_ptr and write the tag.  The
                # tuple starts out uninitialized (filled in by later stores).
                tag = self.tuple_tag(ty)
                instrs = [
                    Instr('movq', [Global('free_ptr'), Reg('r11')]),
                    Instr('addq', [Immediate(8 * (n + 1)), Global('free_ptr')]),
                    Instr('movq', [Immediate(tag), Deref('r11', 0)]),
                ]
                if target != Reg('r11'):
                    instrs.append(Instr('movq', [Reg('r11'), target]))
                return instrs
            case BinOp(left, Mult(), right):
                # Multiplication is commutative, so whichever operand is
                # already in the target can be multiplied in place.
                left_arg = self.select_arg(left)
                right_arg = self.select_arg(right)
                if target == left_arg:
                    return [Instr('imulq', [right_arg, target])]
                if target == right_arg:
                    return [Instr('imulq', [left_arg, target])]
                return [
                    Instr('movq', [left_arg, target]),
                    Instr('imulq', [right_arg, target]),
                ]
            case Call(Name('array_len'), [arg]):
                # The length of an array is stored in bits 2-61 of its tag.
                # Shifting left and then right again clears bits 60-63
                # (the tag bit and the top part of the length field) without
                # needing a 64-bit mask, which would not fit in an immediate.
                src = self.select_arg(arg)
                instrs = []
                if src != Reg('r11'):
                    instrs.append(Instr('movq', [src, Reg('r11')]))
                instrs.extend([
                    Instr('movq', [Deref('r11', 0), target]),
                    Instr('sarq', [Immediate(2), target]),
                    Instr('shlq', [Immediate(4), target]),
                    Instr('shrq', [Immediate(4), target]),
                ])
                return instrs
            case Call(Name('array_load'), [arr, index]):
                # The address of element i is arr + 8 (i + 1): the +1 skips
                # the 8-byte tag.  The address is built in %rax and the
                # loaded value travels through %r11.
                arr_arg = self.select_arg(arr)
                index_arg = self.select_arg(index)
                instrs = []
                if arr_arg != Reg('r11'):
                    instrs.append(Instr('movq', [arr_arg, Reg('r11')]))
                instrs.append(Instr('movq', [index_arg, Reg('rax')]))
                instrs.extend([Instr('addq', [Reg('rax'), Reg('rax')])] * 3)
                instrs.extend([
                    Instr('addq', [Reg('r11'), Reg('rax')]),
                    Instr('movq', [Deref('rax', 8), Reg('r11')]),
                    Instr('movq', [Reg('r11'), target]),
                ])
                return instrs
            case Call(Name('array_store'), [arr, index, value]):
                # As with array_load, but the element is written.  The
                # address lives in %r11 and the value in %rax so that the
                # %rax scratch register used by patch_instructions for
                # large immediates cannot clobber the address.
                arr_arg = self.select_arg(arr)
                index_arg = self.select_arg(index)
                value_arg = self.select_arg(value)
                instrs = [Instr('movq', [index_arg, Reg('r11')])]
                instrs.extend([Instr('addq', [Reg('r11'), Reg('r11')])] * 3)
                instrs.extend([
                    Instr('addq', [arr_arg, Reg('r11')]),
                    Instr('movq', [value_arg, Reg('rax')]),
                    Instr('movq', [Reg('rax'), Deref('r11', 8)]),
                ])
                return instrs
            case AllocateArray(n, ty):
                # Inline array allocation: bump free_ptr and write the tag.
                # The elements start out uninitialized (filled in by the
                # element stores that expose_allocation generated).
                tag = self.array_tag(ty, n)
                instrs = [
                    Instr('movq', [Global('free_ptr'), Reg('r11')]),
                    Instr('addq', [Immediate(8 * (n + 1)), Global('free_ptr')]),
                    Instr('movq', [Immediate(tag), Reg('rax')]),
                    Instr('movq', [Reg('rax'), Deref('r11', 0)]),
                ]
                if target != Reg('r11'):
                    instrs.append(Instr('movq', [Reg('r11'), target]))
                return instrs
            case Call(Name('exit'), []):
                # An out-of-bounds access calls exit(255), which never
                # returns, so no value is produced.
                return [
                    Instr('movq', [Immediate(255), Reg('rdi')]),
                    Callq('exit', 0),
                ]
            case FunRef(label, _):
                # A function reference is the address of its code label;
                # leaq computes that address without touching memory
                # (section 8.8).
                return [Instr('leaq', [Global(label), target])]
            case Call(func, args):
                # A call of a user-defined function goes through the
                # function's address, so it is an indirect call.
                instrs = self.select_arguments(args)
                instrs.append(IndirectCallq(self.select_arg(func), len(args)))
                if target != Reg('rax'):
                    instrs.append(Instr('movq', [Reg('rax'), target]))
                return instrs
            case _:
                raise Exception(
                    'error in select_assign_into, unexpected ' + repr(exp)
                )

    def select_arguments(self, args: list[expr]) -> List[instr]:
        # Move each argument into its argument-passing register
        # (section 8.2.1).  limit_functions packs any arguments beyond the
        # sixth into a tuple, so the six registers below are enough.
        instrs: List[instr] = []
        for (i, arg) in enumerate(args):
            if i >= len(ARG_REGISTERS):
                raise ValueError('select_arguments: too many arguments')
            src = self.select_arg(arg)
            dst = Reg(ARG_REGISTERS[i])
            if src != dst:
                instrs.append(Instr('movq', [src, dst]))
        return instrs

    def select_tail(self, t: stmt, conclusion: str) -> List[instr]:
        match t:
            case Return(value):
                # The return value travels in %rax, then jump to the
                # conclusion of the current function.
                return self.select_assign_into(Reg('rax'), value) + [
                    Jump(conclusion)
                ]
            case TailCall(func, args):
                # Pass the arguments, then pop the frame and jump.  The
                # frame size is not known until register allocation, so we
                # invent the tailjmp pseudo-instruction (section 8.8).
                instrs = self.select_arguments(args)
                instrs.append(TailJump(self.select_arg(func), len(args)))
                return instrs
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
            case Assign([Subscript(tup, Constant(n), Store())], value):
                # Skip the 8-byte tag, then write the n-th element.
                tup_arg = self.select_arg(tup)
                value_arg = self.select_arg(value)
                instrs = []
                if tup_arg != Reg('r11'):
                    instrs.append(Instr('movq', [tup_arg, Reg('r11')]))
                instrs.append(
                    Instr('movq', [value_arg, Deref('r11', 8 * (n + 1))])
                )
                return instrs
            case Assign([lhs], exp):
                return self.select_assign_into(lhs, exp)
            case Collect(n):
                # The collector takes the root stack pointer and the number
                # of bytes requested.
                return [
                    Instr('movq', [Reg('r15'), Reg('rdi')]),
                    Instr('movq', [Immediate(n), Reg('rsi')]),
                    Callq('collect', 2),
                ]
            case _:
                raise Exception('error in select_stmt, unexpected ' + repr(s))

    def select_def(self, f: FunctionDef) -> FunctionDef:
        # Lower one function definition from C_Fun to x86_Def_callq.
        #
        # Pseudocode:
        #   for each block of f, in any order:
        #       instrs = select_stmt for every statement except the tail
        #       instrs += select_tail(tail, f + '_conclusion')
        #       if this is the entry block:
        #           prepend movq from argument registers to parameters
        #   the parameters are removed from the definition
        match f:
            case FunctionDef(name, params, blocks, dl, ty, comment):
                entry = name + '_start'
                conclusion = name + '_conclusion'
                x86_blocks: dict[str, list[instr]] = {}
                for (label, block) in blocks.items():
                    if not block:
                        raise ValueError(f'empty C_Fun block {label}')
                    instrs: List[instr] = []
                    if label == entry:
                        # Turn the parameters into local variables by moving
                        # them out of the argument-passing registers.
                        for ((x, _), reg) in zip(params, ARG_REGISTERS):
                            instrs.append(Instr('movq', [Reg(reg), Variable(x)]))
                    for s in block[:-1]:
                        instrs.extend(self.select_stmt(s))
                    instrs.extend(self.select_tail(block[-1], conclusion))
                    x86_blocks[label] = instrs
                result = FunctionDef(name, [], x86_blocks, dl, ty, comment)
                result.var_types = dict(getattr(f, 'var_types', {}))
                return result
            case _:
                raise Exception('error in select_def, unexpected ' + repr(f))

    def select_instructions(self, p: CProgramDefs) -> X86ProgramDefs:
        # Lower each function definition of C_Fun to the language
        # x86_Def_callq (section 8.8).  The parameters of a function become
        # local variables and every function gets its own start and
        # conclusion labels.
        match p:
            case CProgramDefs(defs):
                return X86ProgramDefs([self.select_def(f) for f in defs])
            case _:
                raise Exception('error in select_instructions, unexpected ' + repr(p))

    ############################################################################
    # Assign Homes
    ############################################################################

    def build_control_flow_graph(self, blocks: dict[str, list[instr]],
                                 conclusion: str = 'conclusion') -> DirectedAdjList:
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
                    # A function's conclusion label is not a block (the
                    # prelude generates it in section 8.11), so it is a
                    # legitimate dangling target.
                    if b == None and i.label != conclusion:
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
            case Instr(iname, [src, dst]) if iname in \
                    ['addq', 'subq', 'xorq', 'andq', 'sarq', 'shlq', 'shrq',
                     'imulq']:
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
            case IndirectCallq(func, n) | TailJump(func, n):
                # A function call with no label: the arity tells which
                # argument registers are read, and the target is read to
                # perform the transfer (section 8.9.1).
                passed = [Reg('rdi'), Reg('rsi'), Reg('rdx'), Reg('rcx'),
                          Reg('r8'), Reg('r9')]
                return self.operand_locations(func) | set(passed[:n])
            case Instr('retq', []):
                return {Reg('rax'), Reg('rsp')}
            case _:
                return set()

    def W(self, i: instr) -> set[location]:
        match i:
            case Instr(iname, [_, dst]) if iname in \
                    ['addq', 'subq', 'xorq', 'andq', 'sarq', 'shlq', 'shrq',
                     'imulq']:
                return self.written_locations(dst)
            case Instr('movq', [_, dst]):
                return self.written_locations(dst)
            case Instr('leaq', [_, dst]):
                # leaq writes its destination register (section 8.8); from a
                # liveness point of view it reads no location.
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
            case Callq(_, _) | IndirectCallq(_, _) | TailJump(_, _):
                # A call may overwrite all caller-saved registers, so any
                # variable live across the call must move to a callee-saved
                # register or to the stack (section 8.9.1).
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
    # A while loop makes the CFG cyclic, so a single pass in reverse
    # topological order is no longer possible (topological order only exists
    # for acyclic graphs). Liveness is a backward analysis whose values form
    # a finite lattice (sets of locations ordered by ⊆, bottom ∅, join ∪),
    # so we iterate the transfer function from ∅ until it stops changing
    # (least fixed point). To reuse the forward worklist algorithm, analyze
    # transpose(CFG): a block's predecessors there are its successors here,
    # so joining their live-before sets gives the block's live-after.
    #
    # Pseudocode:
    #   cfg = build_control_flow_graph(blocks)
    #   live_after = {}                      # instruction -> set of locations
    #   def transfer(label, live):
    #       if label not in blocks: return ∅  # dangling "conclusion"
    #       for i in reverse(blocks[label]):
    #           live_after[i] = live
    #           live = (live − W(i)) ∪ R(i)
    #       return live                       # live-before of the block
    #   analyze_dataflow(transpose(cfg), transfer, ∅, union)
    #   return live_after
    def uncover_live(self, blocks: dict[str, list[instr]],
                     conclusion: str = 'conclusion') -> dict[instr, set[location]]:
        if not isinstance(blocks, dict):
            raise TypeError('uncover_live expects a dictionary of basic blocks')

        for label, instructions in blocks.items():
            if not instructions:
                raise ValueError(f'empty basic block: {label}')

        cfg = self.build_control_flow_graph(blocks, conclusion)

        # build_control_flow_graph only looks at the last two instructions,
        # so validate every jump to keep a mid-block Jump/JumpIf from being
        # silently ignored by the analysis.
        for label, instructions in blocks.items():
            for i in instructions:
                if isinstance(i, (Jump, JumpIf)) and not cfg.has_edge(label, i.label):
                    raise ValueError(f'{i.label} is not a successor of block {label}')

        live_after: dict[instr, set[location]] = {}

        def transfer(label: str, live: set[location]) -> set[location]:
            if label not in blocks:
                return set()            # the absent "conclusion" block
            after = live
            for i in reversed(blocks[label]):
                live_after[i] = after
                after = after.difference(self.W(i)) | self.R(i)
            return after

        analyze_dataflow(transpose(cfg), transfer, set(), lambda a, b: a | b)
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
        var_types: typing.Optional[dict[str, Type]] = None,
    ) -> UndirectedAdjList:
        g = UndirectedAdjList()
        types = var_types if var_types is not None else {}

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
                case Callq('collect', _) | IndirectCallq(_, _) | TailJump(_, _):
                    # The usual rule: the call writes the caller-saved
                    # registers, so they conflict with everything live after.
                    for d in w:
                        for v in lafter:
                            if d != v:
                                add_edge(d, v)
                    # GC rule (sections 7.7, 7.9 and 8.9.2): a heap-
                    # allocated variable (a tuple or an array) that is live
                    # across a call must be spilled so the collector can find
                    # it on the root stack.  Any user-defined function may
                    # allocate memory and therefore call collect, so this
                    # rule applies to indirect calls and tail calls too.
                    # Making the variable conflict with
                    # every callee-saved register leaves it no register to
                    # live in (the caller-saved ones already conflict), so
                    # graph coloring is forced to spill it.
                    # r15 holds the root-stack pointer and is not an
                    # assignable color, so it is intentionally excluded.
                    for v in lafter:
                        if (isinstance(v, Variable)
                                and isinstance(types.get(v.id),
                                               (TupleType, ListType))):
                            for r in [Reg('rbx'), Reg('r12'),
                                      Reg('r13'), Reg('r14')]:
                                add_edge(v, r)
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
                           d: FunctionDef) -> dict[Variable, arg]:
        w = [v for v in g.vertices() if isinstance(v, Variable)]
        d.used_callee = []
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
                if r not in d.used_callee:
                    d.used_callee.append(r)

        # spill variable resize offset: add used_callee size
        spill_offset = len(d.used_callee) * 8
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

    # Register allocation is a per-function activity (section 8.9): the
    # liveness sets, the interference graph and the resulting homes never
    # cross a function boundary, and each function gets its own stack frame
    # (spills, callee-saved registers and root-stack slots).
    def assign_homes_def(self, d: FunctionDef) -> FunctionDef:
        # Pseudocode:
        #   homes = all_home_vars(blocks)
        #   live_after = uncover_live(blocks)
        #   g = build_interference(blocks, live_after, d.var_types)
        #   mov = move_related_graph(homes, blocks)
        #   home = allocate_registers(g, mov, d)    # also sets d.used_callee
        #   move heap-allocated rbp spills to the root stack (-8(%r15) ...)
        #   d.root_stack_size = 8 * number_of_root_spills
        #   replace every Variable by its home
        #   d.stack_size = compute_stack_size(homes, d.used_callee)
        match d:
            case FunctionDef(name, params, blocks, dl, ty, comment) \
                    if isinstance(blocks, dict):
                var_types = dict(getattr(d, 'var_types', {}))
                homes = self.all_home_vars(blocks)
                live_after = self.uncover_live(blocks, name + '_conclusion')

                interference = self.build_interference(
                    blocks, live_after, var_types)
                move_graph = self.move_related_graph(homes, blocks)
                home = self.allocate_registers(interference, move_graph, d)

                # Sections 7.7, 7.9 and 8.9.2: ordinary spills live below
                # %rbp, but heap-allocated (tuple- or array-typed) spills
                # must live on the root stack -- the only stack the
                # collector scans.  r15 points just past the reserved
                # root-stack area (the prelude sets it up in 7.8), so the
                # k-th slot is -8*k(%r15).
                #
                # pseudocode:
                #   root = 0
                #   for v in sorted(home):                # deterministic order
                #       if home[v] is an rbp spill and var_types[v] is a
                #          tuple or an array:
                #           root += 1; home[v] = Deref('r15', -8 * root)
                #   d.root_stack_size = 8 * root
                root_spills = 0
                for variable in sorted(home, key=lambda v: v.id):
                    location = home[variable]
                    if (isinstance(location, Deref)
                            and location.reg == 'rbp'
                            and location.offset < 0
                            and isinstance(var_types.get(variable.id),
                                           (TupleType, ListType))):
                        root_spills += 1
                        home[variable] = Deref('r15', -8 * root_spills)
                d.root_stack_size = 8 * root_spills

                def assign_arg(a: arg) -> arg:
                    if isinstance(a, Variable):
                        if a not in home:
                            raise KeyError(f'no home assigned to {a}')
                        return home[a]
                    return a

                def assign_instr(i: instr) -> instr:
                    match i:
                        case Instr(iname, args):
                            return Instr(iname, [assign_arg(a) for a in args])
                        case IndirectCallq(func, n):
                            return IndirectCallq(assign_arg(func), n)
                        case TailJump(func, n):
                            return TailJump(assign_arg(func), n)
                        case _:
                            return i

                for label, block in blocks.items():
                    blocks[label] = [assign_instr(i) for i in block]

                d.stack_size = self.compute_stack_size(
                    list(home.values()), d.used_callee)
                return d
            case _:
                raise Exception('error in assign_homes_def, unexpected '
                                + repr(d))

    def assign_homes(self, p: X86ProgramDefs) -> X86ProgramDefs:
        # Every function definition is allocated separately; there is no
        # top-level code any more (section 8.9.3).
        match p:
            case X86ProgramDefs(defs):
                return X86ProgramDefs([self.assign_homes_def(d) for d in defs])
            case _:
                raise Exception('error in assign_homes, unexpected ' + repr(p))

    ############################################################################
    # Remove Jumps
    ############################################################################

    # Merge a basic block B into its unique predecessor P when P ends with
    # `Jump(B)`.  The trailing jump is redundant because control already falls
    # through from P into B's first instruction, so we delete the jump and
    # append B's instructions to P.
    #
    # A block can also be reached by a conditional branch, so merging is
    # allowed only when B's sole incoming edge is that unconditional jump.
    # The edge map therefore scans every instruction of a block, not just
    # its last two: once a merge puts a conditional branch in the middle of
    # a block, its target must still count as a predecessor.
    #
    # Both the input and the output are X86ProgramDefs (section 8.9): a
    # program is a list of function definitions, and every definition is merged
    # independently - a block dictionary belongs to one function, so a jump
    # never crosses a function boundary.  The labels `<function>_conclusion`
    # are still dangling at this stage (the prelude/conclusion pass creates
    # those blocks in section 8.11), so a target that is not a block in the
    # current dictionary is not an edge.

    def remove_jumps_blocks(self, body: dict[str, list[instr]]) -> None:
        """Merge a basic block into its unique predecessor.

        Pseudocode:

            edges = {}                       # block -> [(predecessor, kind)]
            for each block P in body:
                for every instruction in P:  # including mid-block branches
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
            # the block dictionary is modified in place
        """
        while True:
            # Collect the incoming edges of every block so that we can
            # identify the blocks that have a unique predecessor.
            edges: dict[str, list[tuple[str, str]]] = {
                label: [] for label in body}
            for p_label, instrs in body.items():
                # Scan every instruction, not just the last two: an
                # earlier merge may have left a conditional branch in
                # the middle of the block, and its target is still a
                # real predecessor.  Missing that edge would make the
                # target look mergeable, and a later merge would delete
                # it while the mid-block branch still refers to it.
                for i in instrs:
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

    def remove_jumps(self, p: X86ProgramDefs) -> X86ProgramDefs:
        match p:
            case X86ProgramDefs(defs):
                for d in defs:
                    if isinstance(d.body, dict):
                        self.remove_jumps_blocks(d.body)
                return p
            case _:
                raise Exception('error in remove_jumps, unexpected '
                                + repr(p))

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

    # Size of the root stack that main passes to initialize().  Unlike the
    # heap (which the collector doubles whenever an allocation does not fit),
    # the root stack never grows: the runtime asserts rootstack_begin <= %r15
    # < rootstack_end every time collect runs.  So this must be strictly
    # larger than the number of root slots the program uses.  65536 bytes =
    # 8192 slots, matching the book, and is the budget shared by all functions
    # once function calls start spilling to the root stack.
    ROOTSTACK_INIT_SIZE = 65536
    # Initial heap size passed to initialize().  The collector doubles the
    # heap on demand, so this only controls how often the first collections
    # happen; the book's Figure 7.17 deliberately starts with a tiny heap.
    HEAP_SIZE = 16

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        used_callee = p.used_callee
        root_stack_size = p.root_stack_size
        assert root_stack_size % 8 == 0, \
            'root_stack_size must be a multiple of 8 bytes'

        # The GC only knows about pointers stored on the root stack, so before
        # main starts we must:
        #   1. call initialize(rootstack_size, heap_size) to set up the
        #      globals free_ptr, fromspace_end and rootstack_begin;
        #   2. load rootstack_begin into %r15, the root-stack pointer.  The
        #      root stack grows upward: after zeroing, %r15 is advanced once
        #      past main's slots, and main addresses them as -8(%r15),
        #      -16(%r15), ... relative to that advanced pointer;
        #   3. zero every root slot.  collect may run before a variable is
        #      initialized, and the GC must not follow garbage as a pointer.
        #      Zeroing emits one movq/addq pair per reserved slot; a compact
        #      REP STOSQ variant is kept commented out below.
        # Reserve max(ROOTSTACK_INIT_SIZE, root_stack_size + 8) bytes, rounded
        # up to 64 (the runtime requires multiples of 64).  The +8 guarantees
        # the collector's strict %r15 < rootstack_end assertion.
        def prelude(stack_size, root_stack_size) -> List[instr]:
            instrs = [
                Instr('pushq', [Reg('rbp')]),
                Instr('movq', [Reg('rsp'), Reg('rbp')]),
            ]
            instrs.extend(Instr('pushq', [reg]) for reg in used_callee)
            instrs.append(Instr('subq', [Immediate(stack_size), Reg('rsp')]))
            rootstack_arg = align(
                max(self.ROOTSTACK_INIT_SIZE, root_stack_size + 8), 64)
            instrs.extend([
                Instr('movq', [Immediate(rootstack_arg), Reg('rdi')]),
                Instr('movq', [Immediate(self.HEAP_SIZE), Reg('rsi')]),
                Callq('initialize', 2),
                Instr('movq', [Global('rootstack_begin'), Reg('r15')]),
            ])

            if root_stack_size > 0:
                for _ in range(root_stack_size // 8):
                    instrs.extend([
                    Instr('movq', [Immediate(0), Deref('r15', 0)]),
                    Instr('addq', [Immediate(8), Reg('r15')]),
                ])
                '''
                # Zero the reserved root slots with a single REP STOSQ instead
                # of one movq/addq pair per slot.  %rax is the value, %rcx the
                # quadword count and %rdi the destination; all three are dead
                # before `start` runs, and DF is 0 per the ABI.
                instrs.extend([
                    Instr('movq', [Reg('r15'), Reg('rdi')]),
                    Instr('movq', [Immediate(0), Reg('rax')]),
                    Instr('movq', [Immediate(root_stack_size // 8), Reg('rcx')]),
                    Instr('rep', ['stosq']),
                    Instr('addq', [Immediate(root_stack_size), Reg('r15')]),
                ])
                '''
            instrs.append(Jump('start'))
            return instrs

        # Unwind the root stack first: it points past main's spill slots, and
        # the conclusion must remove the slots main reserved before returning.
        def conclusion(stack_size, root_stack_size) -> List[instr]:
            instrs = [Instr('subq', [Immediate(root_stack_size), Reg('r15')])]
            instrs.append(Instr('addq', [Immediate(stack_size), Reg('rsp')]))
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
                main_instrs = prelude(p.stack_size, root_stack_size)
                new_body = {'main': main_instrs, 'start': body['start']}
                body.pop('start')
                for label, block in body.items():
                    new_body[label] = block
                new_body['conclusion'] = conclusion(
                    p.stack_size, root_stack_size)
                p.body = new_body
                return p
            case _:
                raise Exception('error in prelude_and_conclusion, unexpected ' + repr(p))
