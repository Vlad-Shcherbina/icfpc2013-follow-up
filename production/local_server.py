import logging
log = logging.getLogger('local_server')

import z3, terms, z3_utils


class Server(object):
    def __init__(self, problems, check_with_real_server=False):
        '''
        If check_with_real_server is True, will also confirm the guess with
        the real server. The problem must be a fresh training problem in that
        case, obviously.
        '''
        self.problem_iter = iter(problems)
        self.compiled_problems = {}
        self.solver = z3.Solver()
        self.z3_x = z3.BitVec('x', 64)
        if check_with_real_server:
            from real_server import Server as RealServer
            self.real_server = RealServer([])
        else:
            self.real_server = None

    def get_problem(self):
        return next(self.problem_iter, None)

    def get_all_problems(self):
        return list(self.problem_iter)

    def request_eval(self, problem, xs):
        parsed, _compiled = self._get_compiled_problem(problem)

        assert len(xs) <= 256
        ys = []
        for x in xs:
            assert 0 <= x < 2 ** 64
            y = terms.apply_lambda(parsed, {}, x)
            ys.append(y)
        return ys

    def guess(self, problem, program):
        parsed, compiled = self._get_compiled_problem(problem)

        test_parsed = terms.parse_term(program)
        lam, (arg,), body = test_parsed
        assert lam == terms.LAMBDA
        test_compiled = z3_utils.term_to_z3(body, {arg: self.z3_x})

        solver = self.solver
        solver.reset()
        log.debug('Z3: checking program equivalence')
        solver.add(compiled != test_compiled)
        r = solver.check()
        if r == z3.unsat:
            log.info('Z3: yay, equivalent!\n    submitted: {!r}\n    secret   : {!r}'.format(
                    terms.term_to_str(test_parsed), terms.term_to_str(parsed)))
            # emulate the real server, refuse to do anything with a solved problem.
            self.compiled_problems[problem.id] = 'solved'
            if self.real_server:
                log.debug('verifying with the real server')
                res, _, _ = self.real_server.guess(problem, program)
                assert res, 'Whooops, real server disagrees!'
            return True, None, None
        elif r == z3.unknown:
            print 'failed to prove'
            print solver.model()
            assert False
        else:
            assert r == z3.sat
            x = solver.model()[self.z3_x]
            if x is None:
                x = 0
            else:
                x = int(x.as_string())
            log.debug('Z3: counterexample: {!r}'.format(x))
            if self.real_server:
                log.debug('verifying with the real server')
                res, _, _ = self.real_server.guess(problem, program)
                assert not res, 'Whooops, real server disagrees!'
            return False, x, terms.apply_lambda(parsed, {}, x)


    def _get_compiled_problem(self, problem):
        res = self.compiled_problems.get(problem.id, None)
        assert res is not 'solved', 'LocalServer: problem {!r} already solved!'.format(problem.id)
        if res is not None: return res

        parsed = terms.parse_term(problem.solution)
        lam, (arg,), body = parsed
        assert lam == terms.LAMBDA

        compiled = z3_utils.term_to_z3(body, {arg: self.z3_x})
        return (parsed, compiled)
