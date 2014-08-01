import math
import pytest


@pytest.fixture
def Point():
    class Point:
        def __init__(self, x, y):
            self.x = x
            self.y = y

        def distance(self, other):
            return math.sqrt((self.x - other.x)**2 + (self.y - other.y)**2)

        def __repr__(self):
            return "Point(%r, %r)" % (self.x, self.y)

    return Point


@pytest.fixture
def almost():
    __tracebackhide__ = True
    def _almost(value, expected):
        return abs(value - expected) < 1e-6
    return _almost
