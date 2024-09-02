# pylint: disable=missing-class-docstring,no-self-use
from __future__ import annotations

import logging
from unittest import TestCase, main

import claripy

l = logging.getLogger("claripy.test.solver")


def raw_hybrid_solver(reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    s = claripy.SolverHybrid()

    x = claripy.BVS("x", 32, min=0, max=10, stride=2)
    y = claripy.BVS("y", 32, min=20, max=30, stride=5)

    # TODO: for now, the stride isn't respected in symbolic mode, but we'll fix that next.
    # until we do, let's add constraints
    s.add(x <= 10)
    s.add(x % 2 == 0)
    s.add(y >= 20)
    s.add(y <= 30)
    s.add((y - 20) % 5 == 0)
    s.add(x != 8)

    assert sorted(s.eval(x, 20, exact=False)) == [0, 2, 4, 6, 8, 10]
    assert sorted(s.eval(x, 20)) == [0, 2, 4, 6, 10]
    assert sorted(s.eval(y, 20, exact=False)) == [20, 25, 30]
    assert sorted(s.eval(y, 20)) == [20, 25, 30]

    # test approximate_first option
    s._approximate_first = True
    old_solve_count = claripy.backends.z3.solve_count
    assert sorted(s.eval(x, 20)) == [0, 2, 4, 6, 8, 10]
    assert claripy.backends.z3.solve_count == old_solve_count
    s._approximate_first = False

    # now constrain things further so that the VSA overapproximates
    s.add(x <= 4)
    assert sorted(s.eval(x, 20, exact=False)) == [0, 2, 4]
    assert sorted(s.eval(x, 20)) == [0, 2, 4]

    s.add(y >= 27)
    assert s.eval(y, 20, exact=False) == (30,)
    assert s.eval(y, 20) == (30,)

    t = claripy.SolverHybrid()
    x = claripy.BVS("x", 32)
    t.add(x <= 10)
    assert len(t.eval(x, 5, exact=False)) == 5
    assert len(t.eval(x, 5, exact=False)) == 5
    assert len(t.eval(x, 6, exact=False)) == 6
    assert len(t.eval(x, 8, exact=False)) == 8
    assert len(t.eval(x, 99, exact=False)) == 11


def raw_replacement_solver(reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    sr = claripy.SolverReplacement()
    x = claripy.BVS("x", 32)
    assert len(sr.eval(x, 10)) == 10
    sr.add_replacement(x, claripy.BVV(0x101, 32))
    assert sr.eval(x, 10) == (0x101,)

    y = claripy.BVS("y", 32)
    sr.add([y + 1 == 200])
    assert (y + 1).cache_key in sr._replacements
    assert sr._replacement(y + 1) is claripy.BVV(200, 32)

    srb = sr.branch()
    assert len(srb.constraints) == len(sr.constraints)  # pylint:disable=no-member
    assert (y + 1).cache_key in sr._replacements
    assert sr._replacement(y + 1) is claripy.BVV(200, 32)

    sr = claripy.SolverReplacement()
    b = claripy.BoolS("b")
    assert sr._replacement(b) is b
    sr.add(claripy.Not(b))
    assert sr._replacement(b) is claripy.false

    sr = claripy.SolverReplacement(claripy.SolverVSA(), complex_auto_replace=True)
    x = claripy.BVS("x", 64)
    sr.add([x + 8 <= 0xFFFFFFFFFFFFFFFF])
    sr.add([x + 8 >= 0])
    assert sr._replacement(x) is not x


def raw_solver(solver_type, reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    s = solver_type()

    s.simplify()

    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)

    l.debug("adding constraints")

    s.add(x == 10)
    s.add(y == 15)

    # Batch evaluation
    results = s.batch_eval([x + 5, x + 6, 3], 2)
    assert len(results) == 1
    assert results[0][0] == 15
    assert results[0][1] == 16
    assert results[0][2] == 3

    l.debug("checking")
    assert s.satisfiable()
    assert not s.satisfiable(extra_constraints=[x == 5])
    assert s.eval(x + 5, 1)[0] == 15
    assert s.solution(x + 5, 15)
    assert s.solution(x, 10)
    assert s.solution(y, 15)
    assert not s.solution(y, 13)

    shards = s.split()
    assert len(shards) == 2
    assert len(shards[0].variables) == 1
    assert len(shards[1].variables) == 1
    if isinstance(s, claripy.frontend_mixins.ConstraintExpansionMixin) or (
        isinstance(s, claripy.frontends.HybridFrontend)
        and isinstance(s._exact_frontend, claripy.frontend_mixins.ConstraintExpansionMixin)
    ):  # the hybrid frontend actually uses the exact frontend for the split
        assert {len(shards[0].constraints), len(shards[1].constraints)} == {
            2,
            1,
        }  # adds the != from the solution() check
    if isinstance(s, claripy.frontends.ReplacementFrontend):
        assert {len(shards[0].constraints), len(shards[1].constraints)} == {1}

    # test result caching
    s = solver_type()
    s.add(x == 10)
    s.add(y == 15)
    assert not s.satisfiable(extra_constraints=(x == 5,))
    assert s.satisfiable()

    s = solver_type()
    # claripy.expression_backends = [ bc, ba, bz ]
    s.add(claripy.UGT(x, 10))
    s.add(claripy.UGT(x, 20))
    s.simplify()
    assert len(s.constraints) == 1
    # assert str(s.constraints[0]._obj) == "Not(ULE(x <= 20))"

    s.add(claripy.UGT(y, x))
    s.add(claripy.ULT(z, 5))

    # test that duplicate constraints are ignored
    old_count = len(s.constraints)
    s.add(claripy.ULT(z, 5))
    assert len(s.constraints) == old_count

    assert s.max(z) == 4
    assert s.min(z) == 0
    assert s.min(y) == 22
    assert s.max(y) == 2 ** y.size() - 1

    ss = s.split()
    assert len(ss) == 2

    # Batch evaluation
    s.add(y < 24)
    s.add(z < x)  # Just to make sure x, y, and z belong to the same solver, since batch evaluation does not support the
    # situation where expressions belong to more than one solver
    results = s.batch_eval([x, y, z], 20)
    assert set(results) == {
        (21, 23, 1),
        (22, 23, 3),
        (22, 23, 2),
        (22, 23, 4),
        (21, 22, 4),
        (21, 23, 4),
        (22, 23, 0),
        (22, 23, 1),
        (21, 22, 1),
        (21, 22, 3),
        (21, 22, 2),
        (21, 22, 0),
        (21, 23, 0),
        (21, 23, 2),
        (21, 23, 3),
    }

    # test that False makes it unsat
    s = solver_type()
    s.add(claripy.BVV(1, 1) == claripy.BVV(1, 1))
    assert s.satisfiable()
    s.add(claripy.BVV(1, 1) == claripy.BVV(0, 1))
    assert not s.satisfiable()

    # test extra constraints
    s = solver_type()
    x = claripy.BVS("x", 32)
    assert s.eval(x, 2, extra_constraints=[x == 10]) == (10,)
    s.add(x == 10)
    assert not s.solution(x, 2)
    assert s.solution(x, 10)

    # test signed min/max
    s = solver_type()
    x = claripy.BVS("x", 32)
    assert s.min(x, signed=True) == -0x80000000
    assert s.max(x, signed=True) == 0x7FFFFFFF
    s.add(claripy.ULE(x, 0x40000000) | claripy.UGE(x, 0xC0000000))
    assert s.min(x, signed=True) == -0x40000000
    assert s.max(x, signed=True) == 0x40000000

    # test result caching

    if isinstance(s, claripy.frontend_mixins.ModelCacheMixin):
        count = claripy.backends.z3.solve_count

        s = solver_type()
        x = claripy.BVS("x", 32)
        s.add(x == 10)
        assert s.satisfiable()
        assert claripy.backends.z3.solve_count == count
        assert s.eval(x, 1)[0] == 10
        assert claripy.backends.z3.solve_count == count
        s.add(x == 10)
        s.add(x > 9)
        assert s.eval(x, 1)[0] == 10
        assert claripy.backends.z3.solve_count == count

        y = claripy.BVS("y", 32)
        s.add(y < 999)
        assert s.satisfiable()
        assert claripy.backends.z3.solve_count == count
        assert s.eval(y, 1)[0] == 0
        assert claripy.backends.z3.solve_count == count


def raw_solver_branching(solver_type, reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    s = solver_type()
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    s.add(claripy.UGT(x, y))
    s.add(claripy.ULT(x, 10))

    assert s.eval(x, 1)[0] > 0

    t = s.branch()
    if isinstance(s, claripy.frontends.FullFrontend):
        assert s._tls.solver is t._tls.solver
        assert s._finalized
        assert t._finalized
    t.add(x == 5)
    # if isinstance(s, claripy.FullFrontend):
    #   assert t._solver is None

    s.add(x == 3)
    assert s.satisfiable()
    t.add(x == 3)
    assert not t.satisfiable()

    s.add(y == 2)
    assert s.satisfiable()
    assert s.eval(x, 1)[0] == 3
    assert s.eval(y, 1)[0] == 2
    assert not t.satisfiable()


def raw_combine(solver_type, reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    s10 = solver_type()
    s20 = solver_type()
    s30 = solver_type()
    x = claripy.BVS("x", 32)

    s10.add(x >= 10)
    s20.add(x <= 20)
    s30.add(x == 30)

    assert s10.satisfiable()
    assert s20.satisfiable()
    assert s30.satisfiable()
    assert s10.combine([s20]).satisfiable()
    assert s20.combine([s10]).satisfiable()
    assert s30.combine([s10]).satisfiable()
    assert not s30.combine([s20]).satisfiable()
    assert s30.combine([s10]).eval(x, 1) == (30,)
    assert len(s30.combine([s10]).constraints) == 2


def raw_composite_solver(reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    # pylint:disable=no-member
    s = claripy.SolverComposite()
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)
    c = claripy.And(x == 1, y == 2, z == 3)
    s.add(c)
    assert len(s._solver_list) == 3
    assert s.satisfiable()

    s.add(x < y)
    assert len(s._solver_list) == 2
    assert s.satisfiable()

    s.simplify()
    assert len(s._solver_list) == 3
    assert s.satisfiable()

    s1 = s.branch()
    assert len(s1._solver_list) == 3

    s1.add(x > y)
    assert len(s1._solver_list) == 2
    assert not s1.satisfiable()
    assert len(s._solver_list) == 3
    assert s.satisfiable()

    s.add(claripy.BVV(1, 32) == claripy.BVV(2, 32))
    assert len(s._solver_list) == 3
    assert not s.satisfiable()

    ss = s.branch()
    assert len(ss._solver_list) == 3
    assert not ss.satisfiable()

    s = claripy.SolverComposite()
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)
    c = claripy.And(x == 1, y == 2, z > 3)
    s.add(c)

    if isinstance(s._template_frontend, claripy.frontend_mixins.ModelCacheMixin):
        assert len(s._solver_list) == 3
        count = claripy.backends.z3.solve_count
        assert s.satisfiable()
        assert claripy.backends.z3.solve_count == count + 3
        assert list(s.eval(x + y, 1)) == [3]
        assert claripy.backends.z3.solve_count == count + 3


def raw_minmax(reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    s = claripy.Solver()
    x = claripy.BVS("x", 32)

    assert s.max(x) == 2**32 - 1
    assert s.min(x) == 0
    assert s.satisfiable()


def raw_composite_discrepancy(reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    a = claripy.BVS("a", 8)
    b = claripy.BVS("b", 8)
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)

    xy = x + y
    dst = claripy.BVV(0xBAAAAF50, 32) + xy
    constraints = []
    constraints.append(x <= 0x1)
    constraints.append(x != 0x0)
    constraints.append(claripy.SignExt(24, claripy.If(x > 0x0, a, 0)) != 0xA)
    constraints.append(x < 0x80)
    constraints.append(y <= 0x1)
    constraints.append(x == 0x1)
    constraints.append((0xBAAAAF50 + x) == 0xBAAAAF51)
    constraints.append(y != 0x0)
    constraints.append(claripy.SignExt(24, claripy.If(y > 0x0, b, 0)) != 0xA)
    constraints.append((x + y) < 0x80)
    constraints.append(z <= 0x1)
    constraints.append((x + y) == 0x2)

    sn = claripy.Solver()
    sc = claripy.SolverComposite()

    sn.add(constraints)
    sc.add(constraints)
    assert sn.max(dst) == sc.max(dst)
    assert sn.min(dst) == sc.min(dst)


def raw_ancestor_merge(solver, reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    s = solver()
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)

    s.add(x == 10)
    s.add(y == x)

    p = s.branch()
    q = s.branch()
    p.add(z == 1)
    q.add(z == 2)

    r = p.merge([q], [claripy.true, claripy.true])[-1]
    t = p.merge([q], [p.constraints[-1], q.constraints[-1]], common_ancestor=s)[-1]

    if not isinstance(r, claripy.frontends.CompositeFrontend):
        assert len(r.constraints) == 1
    assert len(t.constraints) == 3
    assert t.constraints[-1].variables == z.variables
    assert t.constraints[-1].op == "Or"
    assert len(t.constraints[-1].args) == 2


def raw_unsat_core(solver, reuse_z3_solver):
    claripy.backends.z3.reuse_z3_solver = reuse_z3_solver

    s = solver(track=True)
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)
    a = claripy.BVS("a", 32)

    s.add(x == y)
    s.add(x == 1)
    s.add(z != a)
    s.add(z == 2)
    s.add(a == 2)

    assert not s.satisfiable()
    unsat_core = s.unsat_core()
    assert len(unsat_core) == 3
    assert unsat_core[0] is not None
    assert unsat_core[1] is not None
    assert unsat_core[2] is not None


#
# Test Classes
#


class StandardTests(TestCase):
    def test_composite_solver_with_strings(self):
        s = claripy.SolverComposite()
        x = claripy.BVS("x", 32)
        y = claripy.BVS("y", 32)
        z = claripy.BVS("z", 32)
        str_1 = claripy.StringS("sym_str_1", 1024)
        c = claripy.And(x == 1, y == 2, z == 3, str_1 == claripy.StringV("cavallo"))
        s.add(c)
        assert len(s._solver_list) == 4
        assert s.satisfiable()
        assert list(s.eval(str_1, 1)) == ["cavallo"]

    def test_minmax_with_reuse(self):
        raw_minmax(True)

    def test_minmax_without_reuse(self):
        raw_minmax(False)

    def test_composite_discrepancy_with_reuse(self):
        raw_composite_discrepancy(True)

    def test_composite_discrepancy_without_reuse(self):
        raw_composite_discrepancy(False)

    def test_model(self):
        x = claripy.BVS("x", 32)
        y = claripy.BVS("y", 32)
        s = claripy.Solver()

        s.add(x < 10)
        assert sorted(s.eval(x, 20)) == list(range(10))
        s.add(y == 1337)
        assert sorted(s.eval(x, 20)) == list(range(10))

    def test_unsatness(self):
        x = claripy.BVS("x", 32)

        s = claripy.Solver()
        s.add(x == 10)
        assert s.satisfiable()
        s.add(claripy.false)
        assert not s.satisfiable()

    def test_simplification_annotations(self):
        s = claripy.Solver()
        x = claripy.BVS("x", 32)

        s.add(x > 10)
        s.add(x > 11)
        s.add((x > 12).annotate(claripy.SimplificationAvoidanceAnnotation()))

        assert len(s.constraints) == 3
        s.simplify()
        assert len(s.constraints) == 2

    def test_zero_division_in_cache_mixin(self):
        # Bug in the caching backend. See issue #49 on github.
        num = claripy.BVS("num", 8)
        denum = claripy.BVS("denum", 8)
        e = claripy.BVS("e", 8)
        s = claripy.Solver()
        s.add(e == 8)
        assert s.satisfiable()
        s.add(claripy.If(denum == 0, 0, num // denum) == e)
        assert s.satisfiable()
        # As a bonus:
        s.add(num == 16)
        assert s.satisfiable()
        s.add(denum == 3)
        assert not s.satisfiable()

    def test_composite_solver_branching_optimizations(self):
        s = claripy.SolverComposite()
        w = claripy.BVS("w", 32)
        x = claripy.BVS("x", 32)
        y = claripy.BVS("y", 32)
        z = claripy.BVS("z", 32)

        s.add(w == 10)
        assert len(s._unchecked_solvers) == 1
        assert s.satisfiable()
        s.add(x == 10)
        assert len(s._unchecked_solvers) == 1

        s2 = s.branch()
        assert len(s2._unchecked_solvers) == 1
        assert s.satisfiable()
        assert len(s._unchecked_solvers) == 0
        assert len(s2._unchecked_solvers) == 1
        s.add(y == 10)
        assert len(s._unchecked_solvers) == 1
        assert len(s2._unchecked_solvers) == 1
        s2.add(z == 10)
        assert len(s._unchecked_solvers) == 1
        assert len(s2._unchecked_solvers) == 2
        assert s2.satisfiable()
        assert len(s._unchecked_solvers) == 1
        assert len(s2._unchecked_solvers) == 0

        s2.add(z == 12)
        assert not s2.satisfiable()
        assert not s2.satisfiable()

    def test_exhaustion(self):
        s = claripy.Solver()
        x = claripy.BVS("x", 32)
        s.add(x >= 19)
        assert s.min(x) == 19

        s = claripy.Solver()
        x = claripy.BVS("x", 32)
        s.add(x <= 19)
        assert s.max(x) == 19

    def test_cached_max(self):
        s = claripy.Solver()
        x = claripy.BVS("x", 32)
        assert not s.constraints
        assert s.max(x) == 0xFFFFFFFF
        assert len(s.constraints) == 1  # ConstraintExpansionMixin will add a new constraint
        assert s.max(x) == 0xFFFFFFFF  # calling it the second time, the cache should not give a different result

        s = claripy.Solver()
        y = claripy.BVS("y", 32)
        s.add(y == 8)
        assert s.eval(y, n=1)[0] == 8
        assert len(s.constraints) == 1
        assert s.max(x) == 0xFFFFFFFF
        assert s.max(x) == 0xFFFFFFFF


#
# Multi-Solver test base classes
#


class Base:
    solver: type[claripy.Solver]

    def test_solver_with_reuse(self):
        raw_solver(self.solver, True)

    def test_solver_without_reuse(self):
        raw_solver(self.solver, False)

    def test_solver_branching_with_reuse(self):
        raw_solver_branching(self.solver, True)

    def test_solver_branching_without_reuse(self):
        raw_solver_branching(self.solver, False)

    def test_combine_with_reuse(self):
        raw_combine(self.solver, True)

    def test_combine_without_reuse(self):
        raw_combine(self.solver, False)

    def test_ancestor_merge_with_reuse(self):
        raw_ancestor_merge(self.solver, True)

    def test_ancestor_merge_without_reuse(self):
        raw_ancestor_merge(self.solver, False)


class UnsatCore(Base):
    def test_unsat_core_with_reuse(self):
        raw_unsat_core(self.solver, True)

    def test_unsat_core_without_reuse(self):
        raw_unsat_core(self.solver, False)


#
# Multi-Solver test base classes
#


class TestSolver(TestCase, UnsatCore):
    solver = claripy.Solver


class TestSolverReplacement(TestCase, Base):
    solver = claripy.SolverReplacement

    def test_replacement_solver_with_reuse(self):
        raw_replacement_solver(True)

    def test_replacement_solver_without_reuse(self):
        raw_replacement_solver(False)


class TestHybrid(TestCase, UnsatCore):
    solver = claripy.SolverHybrid

    def test_hybrid_solver_with_reuse(self):
        raw_hybrid_solver(True)

    def test_hybrid_solver_without_reuse(self):
        raw_hybrid_solver(False)


class TestComposite(TestCase, UnsatCore):
    solver = claripy.SolverComposite

    def test_composite_solver_with_reuse(self):
        raw_composite_solver(True)

    def test_composite_solver_without_reuse(self):
        raw_composite_solver(False)

    def test_composite_solver_child_solvers_transitive_closure(self):
        # https://github.com/angr/angr/issues/3604
        # the child solver must be merged from solvers for the transitive closure of all variable names

        s = claripy.SolverComposite()
        aa = claripy.BVS("aa", 32)
        bb = claripy.BVS("bb", 32)
        cc = claripy.BVS("cc", 32)
        dd = claripy.BVS("dd", 32)
        ee = claripy.BVS("ee", 32)

        s.add(dd[0:0] != 0)
        s.add(bb != 0)
        s.add(aa[15:0] != 0)
        s.add(claripy.If(aa[15:0] >= 0x1, claripy.BVV(0x1, 32), claripy.BVV(0x0, 32)) == 1)
        s.add(0xFFFFFFF + cc + bb == 0)
        s.add(claripy.If((claripy.If(bb == 0x0, bb, dd) | ee) == 0, claripy.BVV(1, 1), claripy.BVV(0, 1)) != 1)

        s.add(dd == 0xB)
        s.simplify()

        s.add(bb == 0x8004)
        s.simplify()

        s.add(ee == 0)
        s.simplify()

        bb_values = s.eval(bb, n=8)
        assert len(bb_values) == 1
        assert bb_values[0] == 0x8004


class TestSolverCacheless(TestCase, UnsatCore):
    solver = claripy.SolverCacheless


if __name__ == "__main__":
    main()
