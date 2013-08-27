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
    result = []
    terms = [
        'x',
        (AND, 'x', 1),
        (PLUS, 'x', 0),
        (AND, (SHL1, 1), 'x'),
        'x',
        (AND, 1, 'x'),
        (PLUS, 'x', 'x'),
        (SHL1, 'x'),
    ]
    for i, t in enumerate(terms):
        result.append(d.find_or_add(t, lambda: i))
    print d.to_str(),

    eq_(result, [0, 1, 0, 3, 0, 1, 6, 6])


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
        d.find_or_add(t, lambda: t)
    print d.to_str()

    unique_terms = list(d.itervalues())

    for i, t1 in enumerate(unique_terms):
        for j in range(i):
            assert not terms_equivalent(t1, unique_terms[j])

    for t in all_terms:
        assert any(terms_equivalent(t, u) for u in unique_terms)

    print len(all_terms), 'terms total'
    print len(unique_terms), 'unique terms'
