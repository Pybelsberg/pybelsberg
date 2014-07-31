import functools
import math
import types
try:
    from unittest import mock
except ImportError:
    import mock

import z3


class WrappingNamespace(dict):
    def __init__(self, solve_cb, *args, **kwargs):
        dict.__init__(self, *args, **kwargs)
        self.solve_cb = solve_cb
        self.patches = {}
    def __getitem__(self, key):
        obj = dict.__getitem__(self, key)
        try:
            if not key.startswith('__'):
                self.wrap(obj, key)
            return obj
        except Exception as e:
            print("ERR", e)
            import traceback;traceback.print_exc()
    def wrap(self, obj, name):
        def setattr_(this, key, value):
            # only use special behaviour for wrapped variables (ie., those
            # mentioned in the @always block)
            #XXX do not use self.patches as it is overridden by the next
            #    @always;  rather: tack a marker, eg. this.__z3vars
            patch = self.patches.get((this, key), None)
            if patch:
                print("SET", this, key, value, "=>", patch)
                self.solve_cb(patch[0] == value)
                return object.__setattr__(this, key, value)
        type(obj).__setattr__ = setattr_
        for attr, val in obj.__dict__.items():
            if attr in type(obj).__dict__:
                continue
            # all variables - class variables = instance variables

            wrapper = [w for t, w in WRAPPERS.items() if isinstance(val, t)]
            if wrapper:
                wrapped = wrapper[0]()
                #XXX make self.patches a dict (obj, attr) -> (wrapped, val)
                self.patches[(obj, attr)] = (wrapped, val)
                setattr(obj, attr, wrapped)
            elif isinstance(val, z3.ExprRef):
                return
            else:
                print("UNWRAPPABLE", prefix, "->", attr, "==", val)

WRAPPERS = {
    float: functools.partial(z3.FreshReal, prefix='R'),
    int: functools.partial(z3.FreshInt, prefix='D'),
    bool: functools.partial(z3.FreshBool, prefix='B'),
}

z3patches = mock.patch('math.sqrt', z3.Sqrt)

def always(func):
    globalz = func.__globals__
    is_patching = False
    solver = z3.Solver()
    solver.set(unsat_core=True)

    def solve(extra_constraint=None):
        nonlocal is_patching, soft_constraints
        if is_patching:
            return
        is_patching = True

        solver.push()
        print('CONTRAINTS AFTER PUSH', [constraint for proposition, constraint in soft_constraints])
        solver.add([constraint for proposition, constraint in soft_constraints])

        # Add extra hard constraints, eg. from obj.__setattr__
        if extra_constraint:
            print("EXTRA CONSTRAINT", extra_constraint)
            solver.add(extra_constraint)

        print("ASSERT", solver)
        check = solver.check()
        print("WE GET HERE", check)
        solution = solver.model()
        solver.pop()

        if check == z3.sat:
            soft_constraints = [s for s in soft_constraints
                                if z3.is_true(solution[s[0]])]
            print("NEW SOFT CONSTRAINTS", soft_constraints)
            print("SATISFIABLE", solution)
            for (obj, attr), (var, _) in namespace.patches.items():
                value = solution[var]
                if isinstance(value, z3.AlgebraicNumRef):
                    value = value.approx()
                value = float(value.as_fraction())
                setattr(obj, attr, value)
        else:
            print("!! UNSATISFIABLE !!")
            #XXX raise
        is_patching = False

    namespace = WrappingNamespace(solve, globalz)
    proxy = types.FunctionType(func.__code__, namespace)
    print("CODE", func.__code__)
    with z3patches:
        is_patching = True
        constraints = proxy()
        if isinstance(constraints, types.GeneratorType):
            constraints = list(constraints)
        is_patching = False

    print("CONSTRAINTS", constraints)
    print("PATCHES", namespace.patches)
    solver.add(constraints)
    solver.push()

    soft_constraints = []
    for var, value in namespace.patches.values():
        proposition = z3.FreshBool()
        constraint = z3.Implies(proposition, var == value)
        soft_constraints.append((proposition, constraint))

    solve()
