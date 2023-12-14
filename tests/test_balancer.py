import claripy


def test_complex_guy():
    guy_wide = claripy.widen(
        claripy.union(
            claripy.union(
                claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)),
                claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32),
            ),
            claripy.union(
                claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)),
                claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32),
            )
            + claripy.BVV(1, 32),
        ),
        claripy.union(
            claripy.union(
                claripy.union(
                    claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)),
                    claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32),
                ),
                claripy.union(
                    claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)),
                    claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32),
                )
                + claripy.BVV(1, 32),
            ),
            claripy.union(
                claripy.union(
                    claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)),
                    claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32),
                ),
                claripy.union(
                    claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)),
                    claripy.union(claripy.BVV(0, 32), claripy.BVV(1, 32)) + claripy.BVV(1, 32),
                )
                + claripy.BVV(1, 32),
            )
            + claripy.BVV(1, 32),
        ),
    )
    guy_inc = guy_wide + claripy.BVV(1, 32)
    guy_zx = claripy.ZeroExt(32, guy_inc)

    s, r = claripy.balancer.Balancer(claripy.backends.vsa, guy_inc <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is guy_wide
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == set([4294967295] + list(range(39)))

    s, r = claripy.balancer.Balancer(claripy.backends.vsa, guy_zx <= claripy.BVV(39, 64)).compat_ret
    assert r[0][0] is guy_wide
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == set([4294967295] + list(range(39)))


def test_simple_guy():
    x = claripy.BVS("x", 32)
    s, r = claripy.balancer.Balancer(claripy.backends.vsa, x <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is x
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert claripy.backends.vsa.max(r[0][1]) == 39

    s, r = claripy.balancer.Balancer(claripy.backends.vsa, x + 1 <= claripy.BVV(39, 32)).compat_ret
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
    s, r = claripy.balancer.Balancer(claripy.backends.vsa, w <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is w
    assert claripy.backends.vsa.min(r[0][1]) == 0
    assert claripy.backends.vsa.max(r[0][1]) == 1  # used to be 39, but that was a bug in the VSA widening

    s, r = claripy.balancer.Balancer(claripy.backends.vsa, w + 1 <= claripy.BVV(39, 32)).compat_ret
    assert s
    assert r[0][0] is w
    assert claripy.backends.vsa.min(r[0][1]) == 0
    all_vals = r[0][1]._model_vsa.eval(1000)
    assert set(all_vals) == {4294967295, 0, 1}


def test_overflow():
    x = claripy.BVS("x", 32)

    print("x + 10 <= 20")
    s, r = claripy.balancer.Balancer(claripy.backends.vsa, x + 10 <= claripy.BVV(20, 32)).compat_ret
    # mn,mx = claripy.backends.vsa.min(r[0][1]), claripy.backends.vsa.max(r[0][1])
    assert s
    assert r[0][0] is x
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == {
        4294967286,
        4294967287,
        4294967288,
        4294967289,
        4294967290,
        4294967291,
        4294967292,
        4294967293,
        4294967294,
        4294967295,
        0,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
    }

    # print("0 <= x + 10")
    # s,r = claripy.balancer.Balancer(claripy.backends.vsa, 0 <= x + 10).compat_ret
    # assert s
    # assert r[0][0] is x

    print("x - 10 <= 20")
    s, r = claripy.balancer.Balancer(claripy.backends.vsa, x - 10 <= claripy.BVV(20, 32)).compat_ret
    assert s
    assert r[0][0] is x
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == set(range(10, 31))

    # print("0 <= x - 10")
    # s,r = claripy.balancer.Balancer(claripy.backends.vsa, 0 <= x - 10).compat_ret
    # assert s
    # assert r[0][0] is x


def test_extract_zeroext():
    x = claripy.BVS("x", 8)
    expr = claripy.Extract(31, 0, claripy.ZeroExt(56, x)) <= claripy.BVV(0xE, 32)
    s, r = claripy.balancer.Balancer(claripy.backends.vsa, expr).compat_ret

    assert s is True
    assert len(r) == 1
    assert r[0][0] is x


def test_complex_case_0():
    #

    """
    <Bool ((0#48 .. Reverse(unconstrained_read_69_16)) << 0x30) <= 0x40000000000000>

    Created by VEX running on the following x86_64 assembly:
    cmp     word ptr [rdi], 40h
    ja      skip
    """

    x = claripy.BVS("x", 16)
    expr = (claripy.ZeroExt(48, claripy.Reverse(x)) << 0x30) <= 0x40000000000000

    s, r = claripy.balancer.Balancer(claripy.backends.vsa, expr).compat_ret

    assert s
    assert r[0][0] is x
    assert set(claripy.backends.vsa.eval(r[0][1], 1000)) == set(range(0, 65 * 0x100, 0x100))


def test_complex_case_1():
    #

    """
    <Bool (0#31 .. (if (0x8 < (0#32 .. (0xfffffffe + reg_284_0_32{UNINITIALIZED}))) then 1 else 0)) == 0x0>

    Created by VEX running on the following S390X assembly:
    0x40062c:       ahik    %r2, %r11, -2
    0x400632:       clijh   %r2, 8, 0x40065c

    IRSB {
       t0:Ity_I32 t1:Ity_I32 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I32 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I32 t11:Ity_I1 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I1

       00 | ------ IMark(0x40062c, 6, 0) ------
       01 | t0 = GET:I32(r11_32)
       02 | t1 = Add32(0xfffffffe,t0)
       03 | PUT(352) = 0x0000000000000003
       04 | PUT(360) = 0xfffffffffffffffe
       05 | t13 = 32Sto64(t0)
       06 | t7 = t13
       07 | PUT(368) = t7
       08 | PUT(376) = 0x0000000000000000
       09 | PUT(r2_32) = t1
       10 | PUT(ia) = 0x0000000000400632
       11 | ------ IMark(0x400632, 6, 0) ------
       12 | t14 = 32Uto64(t1)
       13 | t8 = t14
       14 | t16 = CmpLT64U(0x0000000000000008,t8)
       15 | t15 = 1Uto32(t16)
       16 | t10 = t15
       17 | t11 = CmpNE32(t10,0x00000000)
       18 | if (t11) { PUT(ia) = 0x40065c; Ijk_Boring }
       NEXT: PUT(ia) = 0x0000000000400638; Ijk_Boring
    }
    """

    x = claripy.BVS("x", 32)
    expr = claripy.ZeroExt(
        31, claripy.If(claripy.BVV(0x8, 32) < claripy.BVV(0xFFFFFFFE, 32) + x, claripy.BVV(1, 1), claripy.BVV(0, 1))
    ) == claripy.BVV(0, 32)
    s, r = claripy.balancer.Balancer(claripy.backends.vsa, expr).compat_ret

    assert s is True
    assert len(r) == 1
    assert r[0][0] is x


def test_complex_case_2():
    x = claripy.BVS("x", 32)
    expr = claripy.ZeroExt(
        31, claripy.If(claripy.BVV(0xC, 32) < x, claripy.BVV(1, 1), claripy.BVV(0, 1))
    ) == claripy.BVV(0, 32)
    s, r = claripy.balancer.Balancer(claripy.backends.vsa, expr).compat_ret

    assert s is True
    assert len(r) == 1
    assert r[0][0] is x


if __name__ == "__main__":
    test_overflow()
    test_simple_guy()
    test_widened_guy()
    test_complex_guy()
    test_complex_case_0()
    test_complex_case_1()
    test_complex_case_2()
    test_extract_zeroext()
