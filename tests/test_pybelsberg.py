from unittest import mock
import pytest
import z3
from pybelsberg import always, ConstraintError


def test_basic(Point):
    a = Point(0, 10)

    @always
    def constraint_constant_x():
        return a.x == 20

    assert a.x == 20
    assert a.y == 10

    assert isinstance(a.x, (int, float))
    assert isinstance(a.y, (int, float))


def test_multiple(Point):
    a = Point(0, 10)

    @always
    def constraint_constant_xy():
        yield a.x == 20
        yield a.y == 30

    assert a.x == 20
    assert a.y == 30


def test_complex(Point, almost):
    a = Point(0, 10)
    b = Point(20, 30)

    # poor man's hack for {'a.x': a.x, ...}
    vals = set(enumerate((a.x, a.y, b.x, b.y)))

    @always
    def constraint_distance():
        return a.distance(b) == 100
    print("/"*80)

    assert almost(a.distance(b), 100)

    new = set(enumerate((a.x, a.y, b.x, b.y)))
    # any one attribute can be modified
    assert len(new.difference(vals)) == 1


def test_lambda(Point):
    a = Point(0, 10)

    always(lambda: a.x == 20)

    assert a.x == 20


def test_erroneous_constraint(Point):
    a = Point(0, 0)

    with pytest.raises(ConstraintError):
        @always
        def constraint_conflicting():
            yield a.x == 10
            yield a.x == 20

def test_erroneous_assignment(Point):
    a = Point(0, 10)

    @always
    def constraint_conflicting():
        return a.x == 20

    with pytest.raises(ConstraintError):
        a.x = 30


def test_unaffected(Point, monkeypatch):
    a = Point(0, 0)
    b = Point(0, 0)

    @always
    def constraint_on_a():
        return a.x == a.y  # whatever

    monkeypatch.setattr('z3.Solver.check', mock.Mock())

    b.x = 20
    assert not z3.Solver.check.called


@pytest.mark.skipif(True,
        reason="cannot rely on Z3 modifying variables consistently :(")
def test_retain_maximum_sat_core(Point):
    a = Point(0, 10)
    b = Point(20, 30)

    # see test_complex for a similar approach
    vals = set(enumerate((a.x, a.y, b.x, b.y)))

    @always
    def constraint_distance():
        return a.distance(b) == 100

    new = set(enumerate((a.x, a.y, b.x, b.y)))
    diffs = new.difference(vals)
    assert len(diffs) == 1
    diff, _ = next(iter(diffs))

    a.x = 50
    new = set(enumerate((a.x, a.y, b.x, b.y)))
    diffs2 = new.difference(vals)
    assert len(diffs2) == 2
    # find the change that did not involve a.x
    diff2, _ = next(d for d in diffs2 if d[0] != 0)
    assert diff == diff2


def test_multiple_constraints(Point):
    a = Point(0, 10)

    @always
    def constraint_first():
        return a.x == 20

    @always
    def constraint_second():
        return a.y == 30  # whatever

    print("#"*50)
    with pytest.raises(ConstraintError):
        a.x = 5


def test_conflicting_constraints(Point):
    a = Point(0, 10)

    @always
    def constraint_first():
        return a.x == 20

    with pytest.raises(ConstraintError):
        @always
        def constraint_second():
            return a.x == 30
