import pytest
from pybelsberg import always


@pytest.mark.xfail
def test_typedefs():
    class Person:
        def __init__(self, age):
            self.birthyear = None  # too complicated :(
            self.age = age

        def age_correction(self):
            self.age += 1

    @always({(Person, 'birthyear'): int})
    def constraint_age_is_timedelta():
        Person.birthyear == 2014 - Person.age

    a = Person(44)

    assert isinstance(a.birthyear, int)
    assert a.birthyear == 1970

    a.age = 13
    assert a.birthyear == 2001

    a.age_correction()
    assert a.birthyear == 2000

    a.birthyear = 1914
    assert a.age == 100
