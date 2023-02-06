import claripy

import logging

l = logging.getLogger("claripy.test.replacements")


def test_replacement_solver():
    sr = claripy.SolverReplacement(claripy.SolverVSA(), replace_constraints=True, complex_auto_replace=True)
    x = claripy.BVS("x", 32)

    sr.add(x + 8 == 10)
    assert sr.max(x) == sr.min(x)

    sr2 = sr.branch()
    sr2.add(x + 8 < 2000)
    assert sr2.max(x) == sr2.min(x) == sr.max(x)


def test_contradiction():
    sr = claripy.SolverReplacement(claripy.Solver(), replace_constraints=True)
    x = claripy.BVS("x", 32)

    sr.add(x == 10)
    assert sr.satisfiable()
    assert sr.eval(x, 10) == (10,)

    sr.add(x == 100)
    assert not sr.satisfiable()


def test_branching_replacement_solver():
    #
    # Simple case: replaceable thing first
    #

    x = claripy.BVS("x", 32)
    s0 = claripy.SolverReplacement(claripy.Solver())
    s0.add(x == 0)

    s1a = s0.branch()
    s1b = s0.branch()

    s1a.add(x == 0)
    s1b.add(x != 0)

    assert s1a.satisfiable()
    assert not s1b.satisfiable()

    #
    # Slightly more complex: different ==
    #

    x = claripy.BVS("x", 32)
    s0 = claripy.SolverReplacement(claripy.Solver())
    s0.add(x == 0)

    s1a = s0.branch()
    s1b = s0.branch()

    s1a.add(x == 0)
    s1b.add(x == 1)

    assert s1a.satisfiable()
    assert not s1b.satisfiable()

    #
    # Complex case: non-replaceable thing first
    #

    # x = claripy.BVS('x', 32)
    # s0 = claripy.SolverReplacement(claripy.Solver())
    # s0.add(x != 0)
    # s1a = s0.branch()
    # s1b = s0.branch()
    # s1a.add(x != 0)
    # s1b.add(x == 0)
    # assert s1a.satisfiable()
    # assert not s1b.satisfiable()


if __name__ == "__main__":
    test_branching_replacement_solver()
    test_replacement_solver()
    test_contradiction()
