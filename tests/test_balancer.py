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
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == set([4294967295] + range(39))

    s,r = claripy.balancer.Balancer(claripy.backends.vsa, guy_zx <= claripy.BVV(39, 64)).compat_ret
    assert r[0][0] is guy_wide
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == set([4294967295] + range(39))

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
    all_vals = r[0][1]._model_vsa.eval(1000)
    assert len(all_vals)
    assert min(all_vals) == 0
    assert max(all_vals) == 4294967295
    all_vals.remove(4294967295)
    assert max(all_vals) == 38

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
    all_vals = r[0][1]._model_vsa.eval(1000)
    assert set(all_vals) == set([4294967295, 0, 1])

def test_overflow():
    x = claripy.BVS('x', 32)

    print "x + 10 <= 20"
    s,r = claripy.balancer.Balancer(claripy.backends.vsa, x + 10 <= claripy.BVV(20, 32)).compat_ret
    #mn,mx = claripy.backends.vsa.min(r[0][1]), claripy.backends.vsa.max(r[0][1])
    assert s
    assert r[0][0] is x
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == set([4294967286, 4294967287, 4294967288, 4294967289, 4294967290, 4294967291, 4294967292, 4294967293, 4294967294, 4294967295, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10])

    #print "0 <= x + 10"
    #s,r = claripy.balancer.Balancer(claripy.backends.vsa, 0 <= x + 10).compat_ret
    #assert s
    #assert r[0][0] is x

    print "x - 10 <= 20"
    s,r = claripy.balancer.Balancer(claripy.backends.vsa, x - 10 <= claripy.BVV(20, 32)).compat_ret
    assert s
    assert r[0][0] is x
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == set(range(10, 31))

    #print "0 <= x - 10"
    #s,r = claripy.balancer.Balancer(claripy.backends.vsa, 0 <= x - 10).compat_ret
    #assert s
    #assert r[0][0] is x


if __name__ == '__main__':
    test_overflow()
    test_simple_guy()
    test_widened_guy()
    test_complex_guy()
