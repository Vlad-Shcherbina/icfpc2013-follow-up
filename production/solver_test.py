from local_server import Server
from problem import Problem
from solver import solve


def test():
    problem = Problem(
        id='6nXC7iyndcldO1dvKHbBmDHv',
        size=6, operators=frozenset(['not', 'shr4', 'shr16', 'shr1']))
    problem.solution = '(lambda (x_5171) (shr4 (shr16 (shr1 (not x_5171)))))'

    server = Server([problem])

    solve(problem, server)
