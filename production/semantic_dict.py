from copy import copy

import z3
import z3_utils


class Node(object):
    def __init__(self):
        self.z3t = None
        self.value = None
        self.vars = None
        self.children = None


class SemanticDict(object):
    def __init__(self):
        self.vars = [z3.BitVec(v, 64) for v in 'xyz']
        self.solver = z3.Solver()
        self.root = None

    def find_or_add(self, z3t, value_constructor):
        if self.root is None:
            self.root = Node()
            self.root.z3t = z3t
            self.root.value = value_constructor()
            return self.root.value

        def eval_in_model(t):
            result = model.evaluate(t, model_completion=True)
            return int(result.as_string())

        node = self.root
        while node.children is not None:
            self.solver.reset()
            for var, val in zip(self.vars, node.vars):
                self.solver.add(var == val)
            result = self.solver.check()
            assert result == z3.sat
            model = self.solver.model()
            t = eval_in_model(z3t)
            if t not in node.children:
                leaf = Node()
                leaf.z3t = z3t
                leaf.value = value_constructor()
                node.children[t] = leaf
                return leaf.value

            node = node.children[t]

        self.solver.reset()
        self.solver.add(node.z3t != z3t)
        result = self.solver.check()
        if result == z3.sat:
            model = self.solver.model()
            leaf1 = copy(node)
            leaf2 = Node()
            leaf2.z3t = z3t
            leaf2.value = value_constructor()
            node.z3t = node.value = None

            node.vars = [eval_in_model(v) for v in self.vars]
            node.children = {}
            node.children[eval_in_model(leaf1.z3t)] = leaf1
            node.children[eval_in_model(leaf2.z3t)] = leaf2

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