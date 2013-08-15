from collections import namedtuple

from terms import *


Constraint = namedtuple('Constraint', 'x can_be_zero can_be_one')
class Constraint(Constraint):
    @staticmethod
    def create_precise(x, y):
        return Constraint(x=x, can_be_zero=MASK^y, can_be_one=y)

    def value_satisfies(self, value):
        return (
            value & ~self.can_be_one == 0 and
            (MASK^value) & ~self.can_be_zero == 0)

    def term_satisfies(self, term):
        return self.value_satisfies(evaluate(term, dict(x=self.x)))

    def is_precise(self):
        return self.can_be_zero & self.can_be_one == 0

    def get_precise_value(self):
        assert self.is_precise()
        return self.can_be_one

    def is_trivial(self):
        return self.can_be_zero == self.can_be_one == MASK

    def is_contradictory(self):
        return self.can_be_one|self.can_be_zero != MASK


def filter_with_constraint(terms, constraints):
    return [t for t in terms if all(c.term_satisfies(t) for c in constraints)]


RIGHT_SHIFTS = {SHR1:1, SHR4:4, SHR16:16}
def propagate_unary(op, constraints):
    # return None if unsatisfiable
    result = []
    for c in constraints:
        if op == NOT:
            c1 = Constraint(c.x, c.can_be_one, c.can_be_zero)
            result.append(c1)
        elif op == SHL1:
            if c.can_be_zero & 1 == 0:
                return None
            margin = 1 << 63
            c1 = Constraint(c.x,
                (c.can_be_zero >> 1) | margin, (c.can_be_one >> 1) | margin)
            if not c1.is_trivial():
                result.append(c1)
        elif op in RIGHT_SHIFTS:
            shift = RIGHT_SHIFTS[op]
            if c.can_be_zero >> (64-shift) != (1<<shift) - 1:
                return None
            margin = (1<<shift) - 1
            c1 = Constraint(c.x,
                (c.can_be_zero << shift) & MASK | margin,
                (c.can_be_one << shift) & MASK | margin)
            if not c1.is_trivial():
                result.append(c1)
        else:
            pass
    return result


def propagate_binary1(op, constraints):
    if op in [PLUS, XOR]:
        return []
    elif op == AND:
        return [Constraint(c.x, c.can_be_zero, MASK) for c in constraints]
    elif op == OR:
        return [Constraint(c.x, MASK, c.can_be_one) for c in constraints]
    else:
        assert False, op


def propagate_binary2(op, arg1, constraints):
    result = []
    for c in constraints:
        assert not c.is_contradictory()
        value = evaluate(arg1, dict(x=c.x))
        if op == XOR:
            c1 = Constraint(c.x,
                c.can_be_zero & ~value | c.can_be_one & value,
                c.can_be_one & ~value | c.can_be_zero & value)
            result.append(c1)
        elif op == PLUS:
            ## TODO
            if c.is_precise():
                c1 = Constraint.create_precise(c.x, (c.get_precise_value() - value) % 2**64)
                result.append(c1)
        elif op == AND:
            c1 = Constraint(c.x,
                c.can_be_zero,
                MASK & ~(value & ~c.can_be_one))
            if c1.is_contradictory():
                return None
            result.append(c1)
        elif op == OR:
            c1 = Constraint(c.x,
                MASK & ~(~value & ~c.can_be_zero),
                c.can_be_one)
            if c1.is_contradictory():
                return None
            result.append(c1)
        else:
            assert False
    return result
