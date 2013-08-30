from functools import wraps


class ReversibleIterator(object):
    def __init__(self, iterator):
        self.iterator = iterator
        self.unnexted = []

    def __iter__(self):
        return self

    def next(self, *args):
        if self.unnexted:
            return self.unnexted.pop()
        return self.iterator.next(*args)

    def unnext(self, item):
        self.unnexted.append(item)


def cached(f):
    '''
    Return memoized version of a function

    >>> @cached
    ... def f():
    ...     print 'f was called'
    ...     return 42
    >>> f()
    f was called
    42
    >>> f()
    42
    '''
    cache = {}
    @wraps(f)
    def cached_f(*args):
        args = tuple(args)
        try:
            return cache[args]
        except KeyError:
            cache[args] = result = f(*args)
            return result
    cached_f.cache = cache

    def clear_cache():
        cached_f.cache.clear()
    cached_f.clear_cache = clear_cache

    return cached_f
