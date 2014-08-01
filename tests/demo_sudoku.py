import pytest
from pybelsberg import always, ConstraintError, all_different

class MiniSudoku:
    """4x4 Sudoku with 2x2 subtiles"""
    def __init__(self):
        self.field = [[None] * 4 for _ in range(4)]


# @always
def constraint_sudoku_rules():
    for row in MiniSudoku.field:
        for cell in row:
            yield 1 <= cell <= 4
    for row in range(4):
        yield all_different(MiniSudoku.field[row])
        yield sum(row) == 1+2+3+4
    for col in range(4):
        pass
    for sub in range(4):
        pass


@pytest.mark.xfail
def test_sudoku():
    s = MiniSudoku()
    s[0][0] = 1
    with pytest.raises(ConstraintError):
        s[0][1] = 1
