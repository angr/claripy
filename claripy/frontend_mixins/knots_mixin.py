from ..errors import ClaripyError

class KnotsError(ClaripyError):
    pass

class KnotsMixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.knots = {}

    def add(self, constraints):
        non_knots = []
        knot = None
        for constraint in constraints:
            conflicts = constraint.variables & (set(self.knots) | (knot.args[1].variables if knot is not None else set()))
            if conflicts:
                raise KnotsError(f"Cannot add constraint on knotted variables {conflicts}")

            if constraint.op == 'Knot':
                if knot is None:
                    #if len(knot.args[0].variables) != 1:
                    #    raise KnotsError("Bad knot: must tie exactly one variable")
                    knot = constraint
                    conflicts = self.variables & knot.args[1].variables
                    if conflicts:
                        raise KnotsError(f"Cannot add knot on constrained variables {conflicts}")
                else:
                    raise KnotsError("One knot at a time please!")
            else:
                non_knots.append(constraint)

        if non_knots:
            super().add(non_knots)
        if knot is not None:
            for var in knot.args[1].variables:
                self.knots[var] = knot

    def eval(self, e, n, **kwargs):
        return tuple( r[0] for r in KnotsMixin.batch_eval(self, [e], n=n, **kwargs) )

    def batch_eval(self, e, n, extra_constraints=(), **kwargs):
        if n != 1:
            raise KnotsError("Can't handle eval with n>1 for now. Sorry!")

        extra_constraints = list(extra_constraints)
        for constraint in extra_constraints:
            if constraint.op == 'Knot':
                raise KnotsError("Cannot add knots in extra constraints")
            conflicts = constraint.variables & set(self.knots)
            if conflicts:
                raise KnotsError(f"Cannot add constraint on knotted variables {conflicts}")


        known_equalities = {}  # will be added to each solve to maintain consistency
        pending_expressions = [(expr, None) for expr in e]  # expression to solve, corresponding knot
        untied_knots = set()

        while True:
            batch = []
            for expr, knot in pending_expressions:
                dirty = False
                for v in expr.variables:
                    v_knot = self.knots.get(v, None)
                    if v_knot is not None:
                        v_knot_output = self.get_knot_output(v_knot)
                        if v_knot_output.cache_key not in known_equalities:
                            dirty = True
                            if not any(x[1] is v_knot for x in pending_expressions):
                                pending_expressions.append((v_knot_output, v_knot))

                if not dirty:
                    batch.append((expr, knot))

            if not batch:
                break

            batch_result = super().batch_eval([x for x, _ in batch], n, extra_constraints=extra_constraints, **kwargs)
            for (expr, knot), result in zip(batch, batch_result):
                pending_expressions = [(ex, kn) for ex, kn in pending_expressions if not (ex is expr and kn is knot)]
                extra_constraints.append(expr == result[0])
                known_equalities[expr.cache_key] = result[0]
                if knot is not None:
                    untied_result = self.untie_knot(knot, result[0])
                    untied_expr = self.get_knot_input(knot)
                    extra_constraints.append(untied_expr == untied_result)
                    known_equalities[untied_expr.cache_key] = untied_result

        try:
            return tuple([known_equalities[expr.cache_key]] for expr in e)
        except KeyError:
            raise Exception("Programming error: eval loop terminated without satisfying all expressions")

    def get_knot_input(self, knot):
        return knot.args[1]

    def get_knot_output(self, knot):
        return knot.args[2]

    def untie_knot(self, knot, solved_output):
        return KNOT_INVERSIONS[knot.args[0]](knot, solved_output)

KNOT_INVERSIONS = {}

import math

def inverse_tan(knot, solved_output):
    return math.atan(solved_output)

def inverse_atof(knot, solved_output):
    digits = len(knot.args[1]) // 8
    return format(solved_output, '.' + str(digits) + 'f')[:digits].encode()

KNOT_INVERSIONS['tan'] = inverse_tan
KNOT_INVERSIONS['atof'] = inverse_atof