from pybelsberg import always


class Object:
    pass

a = Object()
a.x = 0

@always
def constraint_ax():
    return a.x == 8

def test_global_access():
    assert a.x == 8
