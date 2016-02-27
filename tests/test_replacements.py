import claripy

import logging
l = logging.getLogger('claripy.test.replacements')

def test_replacement_solver():
    sr = claripy.ReplacementFrontend(claripy.LightFrontend(claripy.backends.vsa), replace_constraints=True, complex_auto_replace=True)
    x = claripy.BVS('x', 32)

    sr.add(x + 8 == 10)
    assert sr.max(x) == sr.min(x)

    sr2 = sr.branch()
    sr2.add(x + 8 < 2000)
    assert sr2.max(x) == sr2.min(x) == sr.max(x)

if __name__ == '__main__':
    test_replacement_solver()
