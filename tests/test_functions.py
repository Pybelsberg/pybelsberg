import pytest
import math
from pybelsberg import always

@pytest.mark.xfail
def test_sqrt(Point):
    a = Point(0, 10)
    @always
    def constraint_square_root():
        return math.sqrt(a.x) == 10

    assert almost(a.x, 100)
