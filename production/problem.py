class Problem(object):
    __slots__ = [
        'id',
        'size',
        'operators', # will be automatically converted to frozenset
        'solution',
        'solved',
    ]

    def __init__(self, id, size, operators):
        self.id = id
        self.size = size
        self.operators = frozenset(operators)
        self.solution = None
        self.solved = None

    def kind(self):
        result = 'size' + str(self.size)
        if 'tfold' in self.operators:
            result += 'tfold'
        elif 'fold' in self.operators:
            result += 'fold'
        return result

    @staticmethod
    def from_json(js):
        result = Problem(
                str(js['id']),
                int(js['size']),
                map(str, js['operators']),
                )
        if 'solved' in js:
            result.solved = js['solved']
        return result

    def __repr__(self):
        attrs = ((s, getattr(self, s, None))
                for s in self.__slots__)
        return 'Problem({})'.format(', '.join(
            '{}={!r}'.format(s, it) for s, it in attrs if it is not None))

