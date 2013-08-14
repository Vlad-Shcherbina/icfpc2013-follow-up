import re

LAMBDA = 'lambda'
IF0 = 'if0'
FOLD = 'fold'
NOT = 'not'
SHL1 = 'shl1'
SHR1 = 'shr1'
SHR4 = 'shr4'
SHR16 = 'shr16'
AND = 'and'
OR = 'or'
XOR = 'xor'
PLUS = 'plus'

CONSTANTS = [0, 1]
UNARY_OPS = [NOT, SHL1, SHR1, SHR4, SHR16]
BINARY_OPS = [AND, OR, XOR, PLUS]

ELEMENTARY_OPS = frozenset(UNARY_OPS + BINARY_OPS)

MASK = 2**64-1


def term_to_str(t):
    if isinstance(t, tuple):
        return '({})'.format(' '.join(map(term_to_str, (elem for elem in t))))
    return str(t)


def apply(op, *args):
    """
    >>> apply(PLUS, 1, 2)
    3L
    """
    if op in UNARY_OPS:
        arg, = args
        if op == NOT:
            return MASK ^ arg
        elif op == SHL1:
            return MASK & (arg << 1)
        elif op == SHR1:
            return arg >> 1
        elif op == SHR4:
            return arg >> 4
        elif op == SHR16:
            return arg >> 16
    elif op in BINARY_OPS:
        arg1, arg2 = args
        if op == AND:
            assert len(args) == 2, args
            return arg1 & arg2
        elif op == OR:
            assert len(args) == 2, args
            return arg1 | arg2
        elif op == XOR:
            assert len(args) == 2, args
            return arg1 ^ arg2
        elif op == PLUS:
            assert len(args) == 2, args
            return (arg1 + arg2) & MASK

    assert False, op


def evaluate(t, env={}):
    if isinstance(t, tuple):
        op = t[0]
        if op in ELEMENTARY_OPS:
            return apply(op, *(evaluate(arg, env) for arg in t[1:]))
        if op == IF0:
            _, cond, then, else_ = t
            if evaluate(cond, env) == 0:
                return evaluate(then, env)
            else:
                return evaluate(else_, env)
        elif op == FOLD:
            _, bytes, start, fn = t
            bytes = evaluate(bytes, env)
            accum = evaluate(start, env)
            for i in range(8):
                byte = (bytes >> i*8) & 255
                accum = apply_lambda(fn, env, byte, accum)
            return accum
        else:
            assert False, t
        return
    if t in CONSTANTS:
        return t
    elif t in env:
        return env[t]
    else:
        assert False, t


def apply_lambda(lambda_expr, env, *args):
    lam, formal_args, body = lambda_expr
    assert lam == LAMBDA
    assert len(formal_args) == len(args)
    env = dict(env)
    env.update(zip(formal_args, args))
    return evaluate(body, env)


def term_size(t):
    if isinstance(t, tuple):
        if t[0] == LAMBDA:
            assert len(t) == 3
            return 1 + term_size(t[2])
        else:
            # fold is covered by this case
            return sum(map(term_size, t))
    return 1


def term_op(t):
    '''
    Implementation of function Op from problem statement.
    '''
    if isinstance(t, tuple):
        if t[0] == LAMBDA:
            assert len(t) == 3
            return term_op(t[2])
        else:
            result = set([t[0]])
            for tt in t[1:]:
                result |= term_op(tt)
            return result
    return set()


def subst(t, replacements={}):
    if t in replacements:
        return replacements[t]
    if isinstance(t, tuple):
        return tuple(
            subst(tt, replacements) for tt in t)
    return t
