from nose.tools import eq_
from nose.tools import assert_raises

from local_server import Server
from problem import Problem


def test():
    problem = Problem(
        id='6nXC7iyndcldO1dvKHbBmDHv',
        size=6, operators=frozenset(['not', 'shr4', 'shr16', 'shr1']))
    problem.solution = '(lambda (x_5171) (shr4 (shr16 (shr1 (not x_5171)))))'

    server = Server([problem])
    xs = [0, 1]
    ys = server.request_eval(problem, xs)
    eq_(ys, [0x7ffffffffff, 0x7ffffffffff])

    result, _, _ = server.guess(problem, '(lambda (x) x)')
    assert not result

    result, _, _ = server.guess(problem, '(lambda (x) (shr16 (shr4 (shr1 (not x)))))')
    assert result

    # Can't guess for problem that is solved already.
    with assert_raises(AssertionError):
        result, _, _ = server.guess(problem, '(lambda (x) x)')
