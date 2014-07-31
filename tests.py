import math
from pybelsberg import always

class Point(object):
    def __init__(self, x, y):
        self.x = x
        self.y = y
    def distance(self, other):
        return math.sqrt((self.x - other.x)**2 )
        # return math.sqrt((self.x - other.x)**2 + (self.y - other.y)**2)
    def __repr__(self):
        return "Point(%s, %s)" % (self.x, self.y)

_last = set()
def _diffs():
    global _last
    new = set([('a.x', a.x), ('a.y', a.y), ('b.x', b.x), ('b.y', b.y)])
    diffs = new.difference(_last)
    _last = diffs
    return len(diffs)

a = Point(10.0, 10.0)
b = Point(0.0, 0.0)
_diffs()

@always
def my_favorite_constraint():
    yield a.distance(b) == 40
print("AFTER @ALWAYS")

# c = Point(0.0, 0.0)
# @always
# def empty_constraint():
#     yield c.distance(c) == 0


# my_favorite_constraint = always(lambda:
#     a.distance(b) == 20
# )

#XXX
#my_favorite_constraint.delete()
#XXX atomic blocks

def assert_almost_equals(first, second, places=7):
    assert round(abs(first - second), places) == 0, \
            "%r ~= %r" % (first, second)


print("a", a, "b", b, "=>", a.distance(b))
assert_almost_equals(a.distance(b), 20)
assert _diffs() == 1, "only one value changed"

print("BEFORE SET a.x = 100")
a.x = 100
assert a.x == 100
assert_almost_equals(a.distance(b), 20)
print("a", a, "b", b, "=>", a.distance(b))

print("BEFORE SET a.x = 101")
a.x = 101
assert_almost_equals(a.distance(b), 20)
print("a", a, "b", b, "=>", a.distance(b))

print("BEFORE SET a.y = 100")
a.y = 100
assert a.y == 100
assert_almost_equals(a.distance(b), 20)
print("a", a, "b", b, "=>", a.distance(b))

import sys;sys.exit()
b_orig = b.x, b.y
a = Point(2.5, 3.5)  # unhook
assert b_orig == b.x, b.y
