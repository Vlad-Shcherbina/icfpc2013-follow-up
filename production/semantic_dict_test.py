from nose.tools import eq_
from nose.plugins.attrib import attr

from terms import *
import z3
import z3_utils
from enum import Enum
from semantic_dict import SemanticDict
from z3_utils import term_to_z3, default_env


def simple_test():
    d = SemanticDict()
    x = z3.BitVec('x', 64)
    result = []
    for i, z3t in enumerate([x, x&1, x+0, 2&x, x, x%2, x+x]):
        result.append(d.find_or_add(z3t, lambda: i))
    print d.to_str(),

    eq_(result, [0, 1, 0, 3, 0, 1, 6])


def terms_equivalent(t1, t2):
    zt1 = term_to_z3(t1, default_env)
    zt2 = term_to_z3(t2, default_env)
    solver = z3.Solver()
    solver.add(zt1 != zt2)
    result = solver.check()
    if result == z3.sat:
        return False
    elif result == z3.unsat:
        return True
    else:
        assert False, (result, zt1, zt2)


@attr('expensive')
def test_with_enum():
    e = Enum(operators=frozenset(
        [NOT, SHL1, SHR4, AND, PLUS, OR, XOR]))
    all_terms = list(e.base_enum(3))

    d = SemanticDict()
    for t in all_terms:
        z3t = term_to_z3(t, default_env)
        d.find_or_add(z3t, lambda: t)
    print d.to_str()

    unique_terms = list(d.itervalues())

    for i, t1 in enumerate(unique_terms):
        for j in range(i):
            assert not terms_equivalent(t1, unique_terms[j])

    for t in all_terms:
        assert any(terms_equivalent(t, u) for u in unique_terms)

    print len(all_terms), 'terms total'
    print len(unique_terms), 'unique terms'
