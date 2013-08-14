import itertools
from random import randrange

from terms import *
from enum import Enum

import logging
logger = logging.getLogger(__name__)


NUMBERS_TO_TEST = [0] + [1 << i for i in [1, 2, 3, 4, 5, 15, 16, 31, 32, 63]]
NUMBERS_TO_TEST.extend([MASK ^ i for i in NUMBERS_TO_TEST])


def random_interesting_number():
    if randrange(2) == 0:
        return randrange(2**64)
    size = randrange(1, 64)
    x = randrange(1 << size)
    if randrange(2) == 0:
        x <<= 64-size
    if randrange(2) == 0:
        x ^= MASK
    return x


def get_new_points(n, known_values):
    xs = []
    for i in NUMBERS_TO_TEST:
        if len(xs) == n:
            break
        if i not in known_values:
            xs.append(i)
    while len(xs) < n:
        x = random_interesting_number()
        if x not in known_values and x not in xs:
            xs.append(x)
    return xs


def solve(problem, server):
    assert 'fold' not in problem.operators
    assert 'tfold' not in problem.operators

    e = Enum(problem.operators)
    candidates = itertools.chain(
        *(e.base_enum(size) for size in range(1, problem.size)))

    known_values = {}
    while True:
        logging.info('request eval')
        xs = get_new_points(256, known_values)
        ys = server.request_eval(problem, xs)
        known_values.update(zip(xs, ys))

        for candidate in candidates:
            for x, y in known_values.items():
                if evaluate(candidate, dict(x=x)) != y:
                    break
            else:
                break
        else:
            assert False, 'no candidates fit known values'

        logging.info('trying candidate {}'.format(term_to_str(candidate)))
        program = '(lambda (x) {})'.format(term_to_str(candidate))
        result, x, y = server.guess(problem, program)
        if result:
            logging.info('problem solved')
            return

        logging.info('wrong guess')
        known_values[x] = y


if __name__ == '__main__':
    from communicate import get_training_problem
    from real_server import Server

    logging.basicConfig(level=logging.INFO)
    logger.info('hi')

    problem = get_training_problem(10, operators=[])

    server = Server([problem])

    solve(problem, server)