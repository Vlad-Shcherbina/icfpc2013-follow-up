from nose.tools import eq_

import z3
from semantic_dict import SemanticDict


def simple_test():
    d = SemanticDict()
    x = z3.BitVec('x', 64)
    result = []
    for i, z3t in enumerate([x, x&1, x+0, 2&x, x, x%2, x+x]):
        result.append(d.find_or_add(z3t, lambda: i))
    print d.to_str(),

    eq_(result, [0, 1, 0, 3, 0, 1, 6])
