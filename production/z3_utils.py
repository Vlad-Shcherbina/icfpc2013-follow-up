import z3

from terms import *


zero56 = z3.BitVecVal(0, 56)

# for convenience
default_env = {v:z3.BitVec(v, 64) for v in 'xyz'}

def term_to_z3(t, env={}):
    if isinstance(t, (int, long)):
        return z3.BitVecVal(t, 64)
    if t in env:
        return env[t]

    assert isinstance(t, tuple), t
    op = t[0]
    if op == PLUS:
        assert len(t) == 3
        return term_to_z3(t[1], env) + term_to_z3(t[2], env)
    if op == AND:
        assert len(t) == 3
        return term_to_z3(t[1], env) & term_to_z3(t[2], env)
    if op == OR:
        assert len(t) == 3
        return term_to_z3(t[1], env) | term_to_z3(t[2], env)
    if op == XOR:
        assert len(t) == 3
        return term_to_z3(t[1], env) ^ term_to_z3(t[2], env)
    elif op == SHL1:
        assert len(t) == 2
        return term_to_z3(t[1], env) << 1
    elif op == SHR1:
        assert len(t) == 2
        return z3.LShR(term_to_z3(t[1], env), 1)
    elif op == SHR4:
        assert len(t) == 2
        return z3.LShR(term_to_z3(t[1], env), 4)
    elif op == SHR16:
        assert len(t) == 2
        return z3.LShR(term_to_z3(t[1], env), 16)
    elif op == NOT:
        assert len(t) == 2
        return ~term_to_z3(t[1], env)
    elif op == IF0:
        assert len(t) == 4
        return z3.If(
            term_to_z3(t[1], env) == 0,
            term_to_z3(t[2], env),
            term_to_z3(t[3], env))
        pass
    elif op == FOLD:
        _, bytes, start, fn = t
        _, (formal_y, formal_z), body = fn

        bytes = term_to_z3(bytes, env)
        accum = term_to_z3(start, env)
        new_env = dict(env)
        for i in range(8):
            new_env[formal_y] = \
                z3.Concat(zero56, z3.Extract(8*i+7, 8*i, bytes))
            new_env[formal_z] = accum
            accum = term_to_z3(body, new_env)
        return accum
    else:
        assert False, (op, t)
