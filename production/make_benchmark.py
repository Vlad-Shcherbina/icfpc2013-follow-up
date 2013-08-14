import json

from communicate import get_training_problem


if __name__ == '__main__':
    problems = []
    for i in range(20):
        p = get_training_problem(size=8, operators=[])
        problems.append(dict(
            problem=dict(id=p.id, size=p.size, operators=list(p.operators)),
            solution=p.solution))
        print p

    with open('../data/easy_benchmark.json', 'w') as fout:
        json.dump(problems, fout, indent=4)

    print 'done'
