from nose.tools import eq_

from terms import *
from enum import Enum


def test_base_enum():
    e = Enum(operators=frozenset([PLUS, OR, NOT]))
    e.leafs = [0, 'x']
    result = []
    for t in e.base_enum(3):
        print t
        result.append(t)

    expected = sorted([
        ('not', ('not', 0)),
        ('not', ('not', 'x')),
        ('plus', 0, 0),
        ('plus', 0, 'x'),
        ('plus', 'x', 'x'),
        ('or', 0, 0),
        ('or', 0, 'x'),
        ('or', 'x', 'x'),
    ])

    eq_(sorted(result), expected)
