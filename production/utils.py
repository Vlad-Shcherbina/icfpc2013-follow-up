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
