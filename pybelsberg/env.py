import contextlib
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


def Abs(number):
    return z3.If(number > 0, number, -number)

def Sum(sequence, start=0):
    return z3.Sum(sequence) + start


MATH_MODULE = mock.patch.multiple('math',
    sqrt = z3.Sqrt,
)
BUILTIN_MODULE = mock.patch.multiple('builtins',
    abs = Abs,
    all = z3.And,
    any = z3.Or,
    sum = z3.Sum,
)


@contextlib.contextmanager
def patch_builtins():
    with contextlib.ExitStack() as ctx:
        ctx.enter_context(MATH_MODULE)
        ctx.enter_context(BUILTIN_MODULE)
        yield
