from copy import copy

import z3
import z3_utils
import stats


class Node(object):
    def __init__(self):
        self.z3t = None
        self.value = None
        self.vars = None
        self.children = None


class SemanticDict(object):
    def __init__(self):
        self.vars = ['x', 'y', 'z']
        self.solver = z3.Solver()
        self.root = None

    def iter_nodes(self):
        def rec(node):
            if node.children is None:
                yield node
            else:
                for c in node.children.values():
                    for n in rec(c):
                        yield n
        if self.root is not None:
            for n in rec(self.root):
                yield n

    def __len__(self):
        return sum(1 for _ in self.iter_nodes())

    def itervalues(self):
        return (node.value for node in self.iter_nodes())

    @staticmethod
    def _make_z3_evaluator(z3t):
        def evaluator(env):
            solver = z3.Solver()
            for k, v in env.items():
                solver.add(z3.BitVec(k, 64) == v)
            result = solver.check()
            assert result == z3.sat
            model = solver.model()
            return z3_utils.eval_in_model(model, z3t)
        return evaluator

    @stats.TimeIt('SemanticDict.find_or_add')
    def find_or_add(self, z3t, value_constructor, evaluator=None):
        if self.root is None:
            self.root = Node()
            self.root.z3t = z3t
            self.root.value = value_constructor()
            return self.root.value

        if evaluator is None:
            evaluator = self._make_z3_evaluator(z3t)

        node = self.root
        while node.children is not None:
            env = dict(zip(self.vars, node.vars))
            t = evaluator(env)
            if t not in node.children:
                leaf = Node()
                leaf.z3t = z3t
                leaf.value = value_constructor()
                node.children[t] = leaf
                return leaf.value

            node = node.children[t]

        self.solver.reset()
        with stats.TimeIt('equivalence check'):
            self.solver.add(node.z3t != z3t)
            result = self.solver.check()
        if result == z3.sat:
            model = self.solver.model()
            leaf1 = copy(node)
            leaf2 = Node()
            leaf2.z3t = z3t
            leaf2.value = value_constructor()
            node.z3t = node.value = None

            node.vars = [
                z3_utils.eval_in_model(model, z3.BitVec(v, 64))
                for v in self.vars]
            node.children = {}

            node.children[z3_utils.eval_in_model(model, leaf1.z3t)] = leaf1
            node.children[z3_utils.eval_in_model(model, leaf2.z3t)] = leaf2

            return leaf2.value

        elif result == z3.unsat:
            return node.value
        else:
            assert False, result

    def to_str(self, value_to_str=str):
        if self.root is None:
            return 'empty'
        result = []
        def rec(node, indent=''):
            if node.children is None:
                result.append(
                    '{}: {}\n'.format(node.z3t, value_to_str(node.value)))
                return
            env = ', '.join(
                '{}=0x{:x}'.format(var, value)
                for var, value in zip(self.vars, node.vars))
            result.append('f({})?\n'.format(env))
            indent += '    '
            for y, child in sorted(node.children.items()):
                result.append(indent + '0x{:016x} -> '.format(y))
                rec(child, indent)
        rec(self.root)
        return ''.join(result)


if __name__ == '__main__':
    d = SemanticDict()
    x = z3.BitVec('x', 64)
    for i, z3t in enumerate([x, x&1, x+0, 2&x]):
        print d.find_or_add(z3t, lambda: i)

    print d.to_str()
