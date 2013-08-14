import logging
logger = logging.getLogger('real_server')

import communicate


class Server(object):
    def __init__(self, problems):
        self.problem_iter = iter(problems)

    def get_problem(self):
        return next(self.problem_iter)

    def get_all_problems(self):
        return list(self.problem_iter)

    def request_eval(self, problem, xs):
        # TODO: code duplication with communicate.eval_program
        for x in xs:
            assert 0 <= x < 2 ** 64
        assert len(xs) <= 256

        data = dict(id=problem.id, arguments=['0x{:x}'.format(x) for x in xs])
        r = communicate.send('eval', data)
        assert len(r['outputs']) == len(xs)
        return [int(y, 16) for y in r['outputs']]

    def guess(self, problem, program):
        assert program.startswith('(lambda')
        r = communicate.send('guess', dict(id=problem.id, program=program))
        if r['status'] == 'win':
            return True, None, None
        elif r['status']:
            x, y1, y2 = r['values']
            logger.info('wrong guess: f({}) = {}, not {}'.format(x, y1, y2))
            x = int(x, 16)
            y1 = int(y1, 16)
            return False, x, y1

        assert False, r
