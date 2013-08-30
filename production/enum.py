from terms import *
from constraints import Constraint, filter_with_constraint
from constraints import propagate_unary, propagate_binary1, propagate_binary2
from semantic_dict import SemanticDict
import unique_db
import stats

import logging
logger = logging.getLogger(__name__)


class Enum(object):
    def __init__(self, operators):
        self.leafs = [0, 1, 'x']
        self.unary_ops = frozenset(UNARY_OPS) & operators
        self.binary_ops = frozenset(BINARY_OPS) & operators

    def base_enum(self, size, constraints=[]):
        if size < 1:
            return

        if size == 1:
            for t in filter_with_constraint(self.leafs, constraints):
                yield t
            return

        stats.add_value('base_enum', 1)
        for op in self.unary_ops:
            constraints1 = propagate_unary(op, constraints)
            if constraints1 is None:
                stats.add_value('cut ({} *), size={}'.format(op, size), 1)
                continue
            for t in self.base_enum(size-1, constraints=constraints1):
                yield (op, t)

        if size < 3:
            return
        for op in self.binary_ops:
            constraints1 = propagate_binary1(op, constraints)
            if constraints1 is None:
                stats.add_value('cut ({} * *), size={}'.format(op, size), 1)
                continue
            for size1 in range(1, size):
                size2 = size - 1 - size1
                if size2 < size1:
                    continue  # commutativity
                for t1 in self.base_enum(size1, constraints=constraints1):
                    constraints2 = propagate_binary2(op, t1, constraints)
                    if constraints2 is None:
                        stats.add_value('cut ({} t1 *), size={}'.format(op, size), 1)
                        continue
                    for t2 in self.base_enum(size2, constraints=constraints2):
                        if size1 == size2 and t1 > t2:
                            continue  # commutativity
                        if op == PLUS:
                            if not all(c.term_satisfies((op, t1, t2)) for c in constraints):
                                stats.add_value('cut (plus t1 t2), size={}'.format(size), 1)
                                #logging.info('cut (plus {} {})'.format(term_to_str(t1), term_to_str(t2)))
                                continue  # constraints for PLUS are insufficient
                        else:
                            assert all(c.term_satisfies((op, t1, t2)) for c in constraints)
                        yield (op, t1, t2)

        if size < 4:
            return
        for t in self.enum_if0(size, constraints=constraints):
            yield t

    def enum_if0(self, size, constraints=[]):
        if size < 4:
            return
        for size1 in range(1, size):
            size23 = size - 1 - size1
            if size23 < 2:
                continue
            for size2 in range(1, size):
                size3 = size23 - size2
                for pred in self.enum_preds(size1):
                    then_cs = []
                    else_cs = []
                    for c in constraints:
                        if evaluate(pred, dict(x=c.x)) == 0:
                            then_cs.append(c)
                        else:
                            else_cs.append(c)

                    for then in self.base_enum(size2, constraints=then_cs):
                        for else_ in self.base_enum(size3, constraints=else_cs):
                            yield (IF0, pred, then, else_)

    def enum_preds(self, size):
        return self.base_enum(size)


class EnumUnique(Enum):
    def __init__(self, operators):
        super(EnumUnique, self).__init__(operators)
        self.operators = operators

    def base_enum(self, size, constraints=[]):
        if size <= 0:
            return []
        db = unique_db.get_db()
        if db.is_complete_for(unique_db.Shape(size, self.operators)):
            return filter_with_constraint(
                db.get_unique_terms(size, self.operators),
                constraints)

        return super(EnumUnique, self).base_enum(size, constraints)


if __name__ == '__main__':
    e = EnumUnique(operators=frozenset([PLUS, OR, NOT, XOR, SHL1]))
    e.leafs = [0, 'x']
    e.precompute_unique(4)
    cnt = 0
    for t in e.base_enum(4):
        print t
        cnt += 1
    print cnt, 'total'
