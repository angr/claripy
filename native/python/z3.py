__all__ = ["Solver", "Z3"]

import typing

from claricpp import *
from expr import *
from backend import Backend
from functools import cache, cached_property
from typing import List, Union, Optional

# TODO: deal with destruction / freeing memory
# TODO: slots!


class Solver:
    """
    The wrapper for a Z3 solver
    """

    def __init__(self, solver):
        self._solver = solver

    @cached_property
    def raw(self):
        """
        Get the raw solver self holds
        Warning: Do not call this function unless you know what you are doing!
        """
        return self._solver


class Z3(Backend):
    """
    The public API for the Z3 backend
    """

    def __init__(self):
        super().__init__(claricpp.claricpp_backend_z3_new())

    def solver(self, timeout: int = 0, *, force_new: bool = False) -> Solver:
        """
        Get a Z3 solver
        :param timeout: The solver timeout
        :param force_new: Do not reuse an old solver
        :return:
        """
        if force_new:
            return Solver(
                claricpp.claricpp_backend_z3_new_tls_solver(self._raw, timeout)
            )
        else:
            return Solver(claricpp.claricpp_backend_z3_tls_solver(self._raw, timeout))

    def add(
        self, solver: Solver, constraints: Union[Expr, List[Expr]], tracked: bool
    ) -> None:
        """
        Add constraints to a solver
        :param solver: The solver to add the constraints to
        :param constraints: A single or list of Expr constraints to add
        :param tracked: Whether these constraints should be tracked in unsat core
        """
        if type(constraints) is Expr:
            add = [i.raw for i in constraints]
            if tracked:
                claricpp.claricpp_backend_z3_add_vec_tracked(
                    self._raw, solver.raw, add, len(add)
                )
            else:
                claricpp.claricpp_backend_z3_add_vec_untracked(
                    self._raw, solver.raw, add, len(add)
                )
        elif tracked:
            claricpp.claricpp_backend_z3_add_tracked(
                self._raw, solver.raw, constraint.raw
            )
        else:
            claricpp.claricpp_backend_z3_add_untracked(
                self._raw, solver.raw, constraint.raw
            )

    def satisfiable(
        self, solver: Solver, extra_constraints: Optional[List[Expr]] = None
    ) -> bool:
        """
        Return true iff solver is satisfiable when subject to extra_constraints
        """
        if extra_constraints is None:
            return bool(claricpp.claricpp_backend_z3_satisfiable(self._raw, solver.raw))
        ec = [i.raw for i in extra_constraints]
        return bool(
            claricpp.claricpp_backend_z3_satisfiable_ec(
                self._raw, solver.raw, ec, len(ec)
            )
        )

    def solution(
        self,
        expr: Expr,
        sol: Expr,
        solver: Solver,
        extra_constraitns: Optional[List[Expr]] = None,
    ) -> bool:
        """
        Return true iff it is possible that sol == expr for solver given extra_constraints
        """
        if extra_constraitns is None:
            return bool(
                claricpp.claricpp_backend_z3_solution(
                    self._raw, expr.raw, sol.raw, solver.raw
                )
            )
        ec = [i.raw for i in extra_constraitns]
        return bool(
            claricpp.claricpp_backend_z3_solution_ec(
                self._raw, expr.raw, sol.raw, solver.raw, ec, len(ec)
            )
        )

    def min(
        self,
        expr: Expr,
        solver: Solver,
        signed: bool,
        extra_constraints: Optional[List[Expr]] = None,
    ) -> int:
        """
        Find the minimum 64-bit value of expr that satisfies solver given extra_constraints.
        :param signed: Determines if this evaluation is done on signed or unsigned values
        """
        if extra_constraints is not None:
            ec = [i.raw for i in extra_constraints]
            if signed:
                return claricpp.claricpp_backend_z3_min_signed_ec(
                    self._raw, expr.raw, solver.raw, ec, len(ec)
                )
            return claricpp.claricpp_backend_z3_min_unsigned_ec(
                self._raw, expr.raw, solver.raw, ec, len(ec)
            )
        elif signed:
            return claricpp.claricpp_backend_z3_min_signed(
                self._raw, expr.raw, solver.raw
            )
        return claricpp.claricpp_backend_z3_min_unsigned(
            self._raw, expr.raw, solver.raw
        )

    def max(
        self,
        expr: Expr,
        solver: Solver,
        signed: bool,
        extra_constraints: Optional[List[Expr]] = None,
    ) -> int:
        """
        Find the maximum 64-bit value of expr that satisfies solver given extra_constraints.
        :param signed: Determines if this evaluation is done on signed or unsigned values
        """
        if extra_constraints is not None:
            ec = [i.raw for i in extra_constraints]
            if signed:
                return claricpp.claricpp_backend_z3_max_signed_ec(
                    self._raw, expr.raw, solver.raw, ec, len(ec)
                )
            return claricpp.claricpp_backend_z3_max_unsigned_ec(
                self._raw, expr.raw, solver.raw, ec, len(ec)
            )
        elif signed:
            return claricpp.claricpp_backend_z3_max_signed(
                self._raw, expr.raw, solver.raw
            )
        return claricpp.claricpp_backend_z3_max_unsigned(
            self._raw, expr.raw, solver.raw
        )

    def unsat_core(self, solver: Solver) -> List[Expr]:
        """
        Get the unsat core Exprs of the solver (unsat core is a z3 term)
        """
        out = claricpp.claricpp_backend_z3_unsat_core(self._raw, solver.raw)
        arr = out.arr
        # TODO: free array but not contents?
        return [Expr(arr[i]) for i in range(arr.len)]

    def eval(
        self,
        expr: Expr,
        solver: Solver,
        n_sol: int,
        extra_constraints: Optional[List[Expr]] = None,
    ) -> List[LazyPrim]:
        """
        Get up to n different possible value of expr given solver and extra_constraints
        """
        if extra_constraints is None:
            out = claricpp.claricpp_backend_z3_eval(self._raw, expr.raw, solver.raw, n)
        else:
            ec = [i.raw for i in extra_constraints]
            out = claricpp.claricpp_backend_z3_eval(
                self._raw, expr.raw, solver.raw, n, ec, len(ec)
            )
        arr = out.arr
        # TODO: free array but not contents?
        return [Prim(arr[i]) for i in range(arr.len)]

    def batch_eval(
        self,
        exprs: List[Expr],
        solver: Solver,
        n_sol: int,
        extra_constraints: Optional[List[Expr]] = None,
    ) -> List[List[LazyPrim]]:
        """
        Evaluates the exprs expr with solver and returns up to n primitive value(s) they correspond to
        :param exprs: The Exprs to find values for
        :param solver: The solver to use
        :param n_sol: Find up to this many solutions
        :param extra_constraints: Additional constraints find primitives must not violate
        :return: A list of up to n different solutions to the list of exprs
        """
        ex = [i.raw for i in exprs]
        if extra_constraints is None:
            out = claricpp.claricpp_backend_z3_batch_eval(
                self._raw, ex, len(ex), solver.raw, n_sol
            )
        else:
            ec = [i.raw for i in extra_constraints]
            out = claricpp.claricpp_backend_z3_batch_eval_ec(
                self._raw, ex, len(ex), solver.raw, n_sol, ec, len(ec)
            )
        # Compose return value
        ret = []
        main_arr = out.arr
        for index in range(out.len):
            inner_arr = main_arr[index].arr
            length = main_arr[index].len
            ret.append([Expr(inner_arr[i]) for i in range(length)])
        # TODO: free array and double array but not contents?
        return ret
