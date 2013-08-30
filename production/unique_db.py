import itertools
import cPickle as pickle
import os

from terms import *
from semantic_dict import SemanticDict
from utils import cached
import stats

import logging
logger = logging.getLogger(__name__)


ALL_OPS = UNARY_OPS + BINARY_OPS + [IF0]
OP_MASK = {op:1<<i for i, op in enumerate(ALL_OPS)}


class Shape(object):
    ''' Represents 'shape' of a problem or term
    (upper limit on size and allowed operators)
    '''
    def __init__(self, size, ops):
        assert size >= 0
        self.size = size
        self.ops_mask = 0
        for op in ops:
            self.ops_mask |= OP_MASK[op]

    def __eq__(self, other):
        return self.size == other.size and self.ops_mask == other.ops_mask

    def __ne__(self, other):
        return not self.__eq__(other)

    __hash__ = None

    def __add__(self, other):
        result = Shape(self.size + other.size, [])
        result.ops_mask = self.ops_mask | other.ops_mask
        return result

    def is_subset(self, other):
        return self.size <= other.size and self.ops_mask & ~other.ops_mask == 0

    def get_ops(self):
        return [op for op, mask in OP_MASK.items() if self.ops_mask & mask]

    def __repr__(self):
        return 'Shape({}, {!r})'.format(self.size, self.get_ops())


class Entry(object):
    def __init__(self, minimal_implementation):
        self.minimal_implementation = minimal_implementation
        self.possible_shapes = []

    def add_possible_shape(self, shape):
        if any(s.is_subset(shape) for s in self.possible_shapes):
            return
        self.possible_shapes = [
            s for s in self.possible_shapes
            if not shape.is_subset(s)]
        self.possible_shapes.append(shape)

    def is_possible_in(self, shape):
        return any(s.is_subset(shape) for s in self.possible_shapes)

    def __repr__(self):
        return 'Entry(impl={}, shapes={})'.format(
            term_to_str(self.minimal_implementation),
            self.possible_shapes)


class UniqueDB(object):
    def __init__(self):
        self.complete_for = [Shape(0, ALL_OPS)]
        self.by_function = SemanticDict()

    def is_complete_for(self, shape):
        return any(shape.is_subset(s) for s in self.complete_for)

    def get_possible_shapes(self, term):
        if term in [0, 1, 'x']:
            return [Shape(1, [])]
        assert isinstance(term, tuple)
        root_shape = Shape(1, [term[0]])
        args = term[1:]
        possible_args_shapes = [
            self.by_function[arg].possible_shapes
            for arg in args]
        result = []
        for ss in itertools.product(*possible_args_shapes):
            result.append(sum(ss, root_shape))
        return result

    def complete(self, shape, all_terms):
        logger.info('completing for {}'.format(shape))
        assert not self.is_complete_for(shape)
        assert self.is_complete_for(Shape(shape.size-1, shape.get_ops()))
        for term in all_terms:
            if term not in self.by_function:
                e = Entry(term)
                self.by_function[term] = e
            else:
                e = self.by_function[term]

            if term_size(term) < term_size(e.minimal_implementation):
                e.minimal_implementation = term

            with stats.TimeIt('update possible shapes'):
                for s in self.get_possible_shapes(term):
                    e.add_possible_shape(s)

        self.complete_for = [
            s for s in self.complete_for
            if not s.is_subset(shape)]
        self.complete_for.append(shape)

    def get_unique_terms(self, exact_size, ops):
        shape = Shape(exact_size, ops)
        smaller_shape = Shape(exact_size-1, ops)
        for e in self.by_function.itervalues():
            if e.is_possible_in(shape) and not e.is_possible_in(smaller_shape):
                yield e.minimal_implementation

    def to_str(self):
        return 'Complete for {}\n{}'.format(self.complete_for, self.by_function.to_str())


FILENAME = '../data/unique_db.pickle'

@cached
def get_db():
    if os.path.exists(FILENAME):
        logger.info('loading {}'.format(FILENAME))
        with open(FILENAME, 'rb') as fin:
            return pickle.load(fin)
    return UniqueDB()


def save_db():
    db = get_db()
    db.by_function.clear_cache()
    logger.info('saving {}'.format(FILENAME))
    with open(FILENAME, 'wb') as fout:
        pickle.dump(db, fout, protocol=2)


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    db = get_db()

    print db.to_str()
    print len(db.by_function), 'unique terms'
