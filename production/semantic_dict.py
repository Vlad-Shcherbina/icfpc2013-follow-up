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


solver = z3.Solver()


class SemanticDict(object):
    def __init__(self):
        self.vars = ['x', 'y', 'z']
        self.root = None
        self.clear_cache()

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

    def __contains__(self, key):
        self.update_cache(key)
        return self.cached_node is not None

    def __getitem__(self, key):
        self.update_cache(key)
        if self.cached_node is None:
            raise KeyError(key)
        return self.cached_node.value

    def __setitem__(self, key, value):
        self.update_cache(key)
        if self.cached_node is None:
            self.cached_adder(value)

            # TODO: make cached_adder return new node, and use it here to
            # update cache instead of invalidating it.
            self.clear_cache()
        else:
            self.cached_node.value = value

    def clear_cache(self):
        self.cached_key = None
        self.cached_node = None
        self.cached_adder = None

    @stats.TimeIt('SemanticDict.update_cache')
    def update_cache(self, term):
        assert term is not None
        if self.cached_key == term:
            return

        if self.root is None:
            def adder(value):
                self.root = Node()
                self.root.term = term
                self.root.value = value
            self.cached_key = term
            self.cached_node = None
            self.cached_adder = adder
            return

        node = self.root
        while node.children is not None:
            env = dict(zip(self.vars, node.vars))
            v = evaluate(term, env)
            if v not in node.children:
                def adder(value):
                    leaf = Node()
                    leaf.term = term
                    leaf.value = value
                    node.children[v] = leaf
                self.cached_key = term
                self.cached_node = None
                self.cached_adder = adder
                return

            node = node.children[v]

        if term == node.term:
            result = z3.unsat
        else:
            solver.reset()
            with stats.TimeIt('equivalence check'):
                node_z3t = z3_utils.term_to_z3(node.term, z3_utils.default_env)
                z3t = z3_utils.term_to_z3(term, z3_utils.default_env)
                solver.add(node_z3t != z3t)
                result = solver.check()

        if result == z3.sat:
            model = solver.model()
            v1 = z3_utils.eval_in_model(model, node_z3t)
            v2 = z3_utils.eval_in_model(model, z3t)

            def adder(value):
                leaf1 = copy(node)
                leaf2 = Node()
                leaf2.term = term
                leaf2.value = value
                node.term = node.value = None

                node.vars = [
                    z3_utils.eval_in_model(model, z3_utils.default_env[v])
                    for v in self.vars]
                node.children = {}

                node.children[v1] = leaf1
                node.children[v2] = leaf2

            self.cached_key = term
            self.cached_node = None
            self.cached_adder = adder

        elif result == z3.unsat:
            self.cached_key = term
            self.cached_node = node
            self.cached_adder = None
        else:
            assert False, result

    def to_str(self, value_to_str=str):
        if self.root is None:
            return 'empty'
        result = []
        def rec(node, indent=''):
            if node.children is None:
                result.append('{}: {}\n'.format(
                    term_to_str(node.term),
                    value_to_str(node.value)))
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
        if t in d:
            print d[t]
        else:
            d[t] = i
            print i

    print d.to_str()
