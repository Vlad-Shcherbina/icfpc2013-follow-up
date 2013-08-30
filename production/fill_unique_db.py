from enum import EnumUnique
import unique_db
from timeit import default_timer

import logging
logger = logging.getLogger(__name__)


def progress_generator(xs):
    xs = list(xs)
    start = default_timer()
    time_to_report = start + 5
    for i, x in enumerate(xs):
        if i and i % 100 == 0 and default_timer() > time_to_report:
            remaining = (default_timer() - start) * (len(xs)-i) / i
            logger.info(
                'progress {}% ({}/{}) (approx {:.1f}s remaining)'
                .format(100*i/len(xs), i, len(xs), remaining))
            time_to_report = default_timer() + 5
        yield x


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)

    db = unique_db.get_db()

    operators = frozenset(unique_db.ALL_OPS)
    e = EnumUnique(operators)
    for i in range(1, 7+1):
        shape = unique_db.Shape(i, operators)
        if not db.is_complete_for(shape):
            db.complete(shape, progress_generator(e.base_enum(i)))
            unique_db.save_db()
            logger.info('unique_db size = {}'.format(len(db.by_function)))
