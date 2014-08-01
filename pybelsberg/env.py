from unittest import mock
import z3


def all_different(lst):
    return z3.And(_all_different(lst))
def _all_different(lst):
    for idx, elem in enumerate(lst):
        for other in lst[idx+1:]:
            yield elem != other

def all_same(lst):
    return z3.And(_all_same(lst))
def _all_same(lst):
    last = _sentinel
    for idx, elem in enumerate(lst[1:]):
        if last == _sentinel:
            continue
        yield last == elem


z3patches = mock.patch('math.sqrt', z3.Sqrt)
