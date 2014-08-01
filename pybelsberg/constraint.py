import types
import z3
from .solver import Solver
from .namespace import WrappingNamespace
from .env import patch_builtins


class Constraints:
    """A collection of constraints.

    :var namespace: Substitute for the global namespace in which the function
                    is normally executed.
    :var inprogress: Marker if a solver run is currently in progress and no
                     further action should be taken.
    :param func: The function returning or yielding the constraints.

    """
    def __init__(self, func):
        self.inprogress = True

        self.namespace = ns = WrappingNamespace(self, func.__globals__)

        # wrap all cells in the closure
        for name, cell in zip(func.__code__.co_freevars, func.__closure__ or ()):
            ns.wrap(cell.cell_contents, name)

        # create a function in a new global namespace
        proxy = types.FunctionType(func.__code__,
                                   globals=ns,
                                   closure=func.__closure__)
        with patch_builtins():
            constraints = proxy()  # !!
            if isinstance(constraints, types.GeneratorType):
                constraints = list(constraints)  # support yield

        self.inprogress = False

        self.solver = Solver(constraints, ns.patches)
        self.solve()

    def solve(self, extra_constraint=None):
        if self.inprogress:
            # already in a solving run,
            # called recursively by `WrappingNamespace.wrap` from `setattr`
            return

        self.inprogress = True
        try:
            # could raise a ConstraintError
            solution = self.solver.solve(extra_constraint)

            for (obj, attr), (var, orig) in self.namespace.patches.items():
                value = solution[var]
                if isinstance(value, z3.AlgebraicNumRef):
                    value = value.approx()
                if isinstance(value, z3.IntNumRef):
                    value = value.as_long()
                if isinstance(value, z3.RatNumRef):
                    value = float(value.as_fraction())
                if value is None:
                    value = orig
                setattr(obj, attr, value)
        finally:
            self.inprogress = False
