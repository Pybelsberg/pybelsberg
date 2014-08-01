import pytest
from pybelsberg import always

@pytest.mark.xfail
def test_class(Point):
    a = Point(0, 10)

    assert a.x == 0
    assert a.y == 10

    @always
    def constraint_equi_point():
        return Point.x == Point.y

    assert a.x == a.y

    b = Point(20, 30)
    assert b.x == b.y


def test_class_new():
    class Equipoint:
        def __init__(self, x, y):
            self.x = x
            self.y = y

            @always
            def constraint_x_is_y():
                return self.x == self.y

    a = Equipoint(10, 20)
    assert a.x == a.y


def test_class_new_inherited():
    class Equipoint:
        def __init__(self, x, y):
            self.x = x
            self.y = y

            @always
            def constraint_x_is_y():
                return self.x == self.y

    class EquipointChild(Equipoint):
        def __init__(self, x, y):
            super().__init__(x, y)
            # super() has to be called before the other constraint because
            # otherwise `self.x` is not defined

            @always
            def constraint_large_x():
                return self.x > 1000

    a = EquipointChild(10, 20)
    assert a.x == a.y
    assert a.x > 1000
