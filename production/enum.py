from terms import *


class Enum(object):
    def __init__(self, operators):
        self.leafs = [0, 1, 'x']
        self.unary_ops = frozenset(UNARY_OPS) & operators
        self.binary_ops = frozenset(BINARY_OPS) & operators

    def base_enum(self, size):
        if size < 1:
            return

        if size == 1:
            for t in self.leafs:
                yield t
            return

        for op in self.unary_ops:
            for t in self.base_enum(size-1):
                yield (op, t)

        if size < 3:
            return
        for op in self.binary_ops:
            for size1 in range(1, size):
                size2 = size - 1 - size1
                if size2 < size1:
                    continue  # commutativity
                for t1 in self.base_enum(size1):
                    for t2 in self.base_enum(size2):
                        if size1 == size2 and t1 > t2:
                            continue  # commutativity
                        yield (op, t1, t2)

        if size < 4:
            return
        for t in self.enum_if0(size):
            yield t

    def enum_if0(self, size):
        if size < 4:
            return
        for size1 in range(1, size):
            size23 = size - 1 - size1
            if size23 < 2:
                continue
            for size2 in range(1, size):
                size3 = size23 - size2
                for pred in self.enum_preds(size1):
                    for then in self.base_enum(size2):
                        for else_ in self.base_enum(size3):
                            yield (IF0, pred, then, else_)

    def enum_preds(self, size):
        return self.base_enum(size)


if __name__ == '__main__':
    e = Enum(operators=frozenset([PLUS, OR, NOT]))
    e.leafs = [0, 1]
    for t in e.base_enum(4):
        print t
