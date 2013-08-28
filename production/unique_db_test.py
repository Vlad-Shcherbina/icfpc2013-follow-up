from nose.tools import eq_

from terms import *
from unique_db import Shape, UniqueDB, ALL_OPS


def test():
    db = UniqueDB()

    leafs = [0, 1, 'x']

    db.complete(Shape(1, ALL_OPS), leafs)

    db.complete(Shape(2, [PLUS]), [])
    db.complete(Shape(3, [PLUS]),
        [(PLUS, arg1, arg2) for arg1 in leafs for arg2 in leafs])
    print db.to_str()

    assert not db.is_complete_for(Shape(2, [NOT]))
    assert db.is_complete_for(Shape(3, []))

    eq_(
        sorted(db.get_unique_terms(3, [PLUS])),
        sorted([(PLUS, 'x', 'x'), (PLUS, 1, 'x'), (PLUS, 1, 1)]))

    db.complete(Shape(2, [SHL1]), [(SHL1, arg) for arg in leafs])
    print db.to_str()

    eq_(list(db.get_unique_terms(2, [PLUS])), [])
    eq_(sorted(db.get_unique_terms(2, [SHL1])),
        sorted([(SHL1, 'x'), (SHL1, 1)]))

    eq_(
        sorted(db.get_unique_terms(3, [PLUS])),
        sorted([(SHL1, 'x'), (PLUS, 1, 'x'), (SHL1, 1)]))
    # Note that we requested terms of size 3 that are only allowed to use PLUS,
    # but got equivalent terms of size 2 with SHL1 instead.
    # It is intentional.
    # We only store one implementation for the whole class of functionally
    # equivalent terms, and we choose smallest implementation, because the
    # opposite situation, when we get larger terms than we requested, is
    # extremely undesirable (because of the possibility to violate maximum
    # term size limit).

    eq_(list(db.get_unique_terms(3, [])), [])
