from pybelsberg import always

class Object(object):
    pass


def test_demo():
    a = Object()
    a.b = 10
    a.c = 20

    @always
    def constraint():
        return a.b + a.c == 50

    assert a.b + a.c == 50

if __name__ == '__main__':
    test_demo()
