import claripy

def test_complex_guy():
    guy_wide = claripy.widen(
        claripy.union(
            claripy.union(
                claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)),
                claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32)
            ),
            claripy.union(
                claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)),
                claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32)
            ) + claripy.BVV(1, 32)
        ),
        claripy.union(
            claripy.union(
                claripy.union(
                    claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)),
                    claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32)
                ),
                claripy.union(
                    claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)),
                    claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32)
                ) + claripy.BVV(1, 32)
            ),
            claripy.union(
                claripy.union(
                    claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)),
                    claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32)
                ),
                claripy.union(
                    claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)),
                    claripy.union(claripy.BVV(0L, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32)
                ) + claripy.BVV(1, 32)
            ) + claripy.BVV(1, 32)
        )
    )
    guy_inc = guy_wide + claripy.BVV(1, 32)
    guy_zx = claripy.ZeroExt(32, guy_inc)

    s,r = claripy.balancer.Balancer(claripy.backends.vsa, guy_inc <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is guy_wide
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert claripy.backends.vsa.max(r[0][1]) == 38

    s,r = claripy.balancer.Balancer(claripy.backends.vsa, guy_zx <= claripy.BVV(39, 64)).compat_ret
    assert r[0][0] is guy_wide
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert claripy.backends.vsa.max(r[0][1]) == 38

def test_simple_guy():
    x = claripy.BVS('x', 32)
    s,r = claripy.balancer.Balancer(claripy.backends.vsa, x <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is x
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert claripy.backends.vsa.max(r[0][1]) == 39

    s,r = claripy.balancer.Balancer(claripy.backends.vsa, x + 1 <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is x
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert claripy.backends.vsa.max(r[0][1]) == 38

def test_widened_guy():
    w = claripy.widen(claripy.BVV(1, 32), claripy.BVV(0, 32))
    s,r = claripy.balancer.Balancer(claripy.backends.vsa, w <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is w
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert claripy.backends.vsa.max(r[0][1]) == 1 # used to be 39, but that was a bug in the VSA widening

    s,r = claripy.balancer.Balancer(claripy.backends.vsa, w + 1 <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is w
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert claripy.backends.vsa.max(r[0][1]) == 1 # used to be 38, but that was a bug in the VSA widening

if __name__ == '__main__':
    test_simple_guy()
    test_widened_guy()
    test_complex_guy()
