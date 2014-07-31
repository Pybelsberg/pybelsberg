pybelsberg
==========

An implementation of Babelsberg allowing constraint-based programming in Python (using the [Z3 theorem prover](http://z3.codeplex.com/)).

See also [Babelsberg/R](https://github.com/timfel/babelsberg-r), [Babelsberg/JS](https://github.com/timfel/babelsberg-js/).

It allows you to write code like the following:

```python
from pybelsberg import always

a = Point(10.0, 10.0)
b = Point(0.0, 0.0)

@always
def my_favorite_constraint():
    yield a.distance(b) == 20

print(a.x, a.y)
print(b.x, b.y)

a.x, a.y = 50
print(a.x, a.y)
print(b.x, b.y)
```
