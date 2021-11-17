import claripy
import unittest


class TestFallbackAbstraction(unittest.Testcae):
    def test_fallback_abstraction(self):
        bz = claripy.backends.z3

        a = claripy.BVV(5, 32)
        b = claripy.BVS('x', 32, explicit_name=True)
        c = a + b
        d = 5 + b
        e = b + 5
        f = b + b
        g = a + a

        assert not a.symbolic
        assert b.symbolic
        assert c.symbolic
        assert d.symbolic
        assert e.symbolic
        assert f.symbolic

        assert type(claripy.backends.concrete.convert(a)) is claripy.bv.BVV
        assert type(claripy.backends.concrete.convert(g)) is claripy.bv.BVV

        self.assertRaise(claripy.errors.BackendError, claripy.backends.concrete.convert, b)
        self.assertRaise(claripy.errors.BackendError, claripy.backends.concrete.convert, c)
        self.assertRaise(claripy.errors.BackendError, claripy.backends.concrete.convert, d)
        self.assertRaise(claripy.errors.BackendError, claripy.backends.concrete.convert, e)
        self.assertRaise(claripy.errors.BackendError, claripy.backends.concrete.convert, f)

        assert str(bz.convert(b)) == 'x'
        assert bz.convert(b).__module__ == 'z3.z3'

        assert str(bz.convert(c)) == '5 + x'
        assert str(bz.convert(d)) == '5 + x'
        assert str(bz.convert(e)) == 'x + 5'
        assert str(bz.convert(f)) == 'x + x'


if __name__ == '__main__':
    unittest.main()
