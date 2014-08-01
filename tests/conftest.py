import math
import pytest


@pytest.fixture
def Point():
    def __init__(self, x, y):
        self.x = x
        self.y = y
    def distance(self, other):
        return math.sqrt((self.x - other.x)**2 + (self.y - other.y)**2)

    return type('Point', (), dict(__init__=__init__, distance=distance))


@pytest.fixture
def almost():
    __tracebackhide__ = True
    def _almost(value, expected):
        return abs(value - expected) < 1e-6
    return _almost
