from copy import copy

import z3

from terms import *
import z3_utils
import stats


class Node(object):
    def __init__(self):
        self.term = None
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

    @stats.TimeIt('SemanticDict.find_or_add')
    def find_or_add(self, term, value_constructor):
        if self.root is None:
            self.root = Node()
            self.root.term = term
            self.root.value = value_constructor()
            return self.root.value

        node = self.root
        while node.children is not None:
            env = dict(zip(self.vars, node.vars))
            v = evaluate(term, env)
            if v not in node.children:
                leaf = Node()
                leaf.term = term
                leaf.value = value_constructor()
                node.children[v] = leaf
                return leaf.value

            node = node.children[v]

        self.solver.reset()
        with stats.TimeIt('equivalence check'):
            node_z3t = z3_utils.term_to_z3(node.term, z3_utils.default_env)
            z3t = z3_utils.term_to_z3(term, z3_utils.default_env)
            self.solver.add(node_z3t != z3t)
            result = self.solver.check()
        if result == z3.sat:
            model = self.solver.model()
            leaf1 = copy(node)
            leaf2 = Node()
            leaf2.term = term
            leaf2.value = value_constructor()
            node.term = node.value = None

            node.vars = [
                z3_utils.eval_in_model(model, z3_utils.default_env[v])
                for v in self.vars]
            node.children = {}

            node.children[z3_utils.eval_in_model(model, node_z3t)] = leaf1
            node.children[z3_utils.eval_in_model(model, z3t)] = leaf2

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
                    '{}: {}\n'.format(node.term, value_to_str(node.value)))
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
    terms = [
        'x',
        (AND, 'x', 1),
        (PLUS, 'x', 0),
        (AND, (SHL1, 1), 'x'),
    ]
    for i, t in enumerate(terms):
        print d.find_or_add(t, lambda: i)

    print d.to_str()
