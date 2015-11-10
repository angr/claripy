import claripy
import nose

def test_smudging():
    x = claripy.BVS('x', 32)
    y = x+1
    nose.tools.assert_true(isinstance(y.args[1], claripy.ast.BV))
    nose.tools.assert_equal(y.args[1].args[0], 1)
    nose.tools.assert_equal(y.args[1].args[1], 32)

    x = claripy.BVS('x', 32)
    y = x*1
    z = y+1
    nose.tools.assert_true(isinstance(y.args[1], claripy.ast.BV))
    nose.tools.assert_equal(y.args[1].args[0], 1)
    nose.tools.assert_equal(y.args[1].args[1], 32)

    nose.tools.assert_true(isinstance(z.args[1], claripy.ast.BV))
    nose.tools.assert_equal(z.args[1].args[0], 1)
    nose.tools.assert_equal(z.args[1].args[1], 32)

    ccc = claripy.If(x > 10, x*3+2, x*4+2)
    nose.tools.assert_true(isinstance(ccc.args[1].args[1], claripy.ast.BV))
    nose.tools.assert_equal(ccc.args[1].args[1].args[0], 2)
    nose.tools.assert_equal(ccc.args[1].args[1].args[1], 32)

def test_expression():
    bc = claripy.backend_concrete

    e = claripy.BVV(0x01020304, 32)
    nose.tools.assert_equal(len(e), 32)
    r = e.reversed
    nose.tools.assert_equal(bc.convert(r), 0x04030201)
    nose.tools.assert_equal(len(r), 32)

    nose.tools.assert_equal([ bc.convert(i) for i in r.chop(8) ], [ 4, 3, 2, 1 ] )

    e1 = r[31:24]
    nose.tools.assert_equal(bc.convert(e1), 0x04)
    nose.tools.assert_equal(len(e1), 8)
    nose.tools.assert_equal(bc.convert(e1[2]), 1)
    nose.tools.assert_equal(bc.convert(e1[1]), 0)

    ee1 = e1.zero_extend(8)
    nose.tools.assert_equal(bc.convert(ee1), 0x0004)
    nose.tools.assert_equal(len(ee1), 16)

    ee1 = claripy.BVV(0xfe, 8).sign_extend(8)
    nose.tools.assert_equal(bc.convert(ee1), 0xfffe)
    nose.tools.assert_equal(len(ee1), 16)

    xe1 = [ bc.convert(i) for i in e1.chop(1) ]
    nose.tools.assert_equal(xe1, [ 0, 0, 0, 0, 0, 1, 0, 0 ])

    a = claripy.BVV(1, 1)
    nose.tools.assert_equal(bc.convert(a+a), 2)

    x = claripy.BVV(1, 32)
    nose.tools.assert_equal(x.length, 32)
    y = claripy.LShR(x, 10)
    nose.tools.assert_equal(y.length, 32)

    r = claripy.BVV(0x01020304, 32)
    rr = r.reversed
    rrr = rr.reversed
    #nose.tools.assert_is(bc.convert(r), bc.convert(rrr))
    #nose.tools.assert_is(type(bc.convert(rr)), claripy.A)
    nose.tools.assert_equal(bc.convert(rr), 0x04030201)
    nose.tools.assert_is(r.concat(rr), claripy.Concat(r, rr))

    rsum = r+rr
    nose.tools.assert_equal(bc.convert(rsum), 0x05050505)

    r = claripy.BVS('x', 32)
    rr = r.reversed
    rrr = rr.reversed
    nose.tools.assert_is(r, rrr)

    # test identity
    nose.tools.assert_is(r, rrr)
    nose.tools.assert_is_not(r, rr)
    ii = claripy.BVS('ii', 32)
    ij = claripy.BVS('ij', 32)
    nose.tools.assert_is(ii, ii)
    nose.tools.assert_is_not(ii, ij)

    si = claripy.SI(bits=32, stride=2, lower_bound=20, upper_bound=100)
    sj = claripy.SI(bits=32, stride=2, lower_bound=10, upper_bound=10)
    sk = claripy.SI(bits=32, stride=2, lower_bound=20, upper_bound=100)
    nose.tools.assert_true(claripy.backend_vsa.identical(si, si))
    nose.tools.assert_false(claripy.backend_vsa.identical(si, sj))
    nose.tools.assert_true(claripy.backend_vsa.identical(si, sk))
    nose.tools.assert_is_not(si, sj)
    nose.tools.assert_is_not(sj, sk)
    nose.tools.assert_is_not(sk, si)

    # test hash cache
    nose.tools.assert_is(a+a, a+a)

    # test replacement
    old = claripy.BVS('old', 32, explicit_name=True)
    new = claripy.BVS('new', 32, explicit_name=True)
    ooo = claripy.BVV(0, 32)

    old_formula = claripy.If((old + 1)%256 == 0, old+10, old+20)
    print old_formula.dbg_repr()
    new_formula = old_formula.replace(old, new)
    print new_formula.dbg_repr()
    ooo_formula = new_formula.replace(new, ooo)

    print ooo_formula.dbg_repr()

    nose.tools.assert_not_equal(hash(old_formula), hash(new_formula))
    nose.tools.assert_not_equal(hash(old_formula), hash(ooo_formula))
    nose.tools.assert_not_equal(hash(new_formula), hash(ooo_formula))

    nose.tools.assert_equal(old_formula.variables, { 'old' })
    nose.tools.assert_equal(new_formula.variables, { 'new' })
    nose.tools.assert_equal(ooo_formula.variables, ooo.variables)

    nose.tools.assert_true(old_formula.symbolic)
    nose.tools.assert_true(new_formula.symbolic)
    nose.tools.assert_true(new_formula.symbolic)

    nose.tools.assert_equal(str(old_formula).replace('old', 'new'), str(new_formula))
    nose.tools.assert_equal(bc.convert(ooo_formula), 20)

    # test dict replacement
    old = claripy.BVS('old', 32, explicit_name=True)
    new = claripy.BVS('new', 32, explicit_name=True)
    c = (old + 10) - (old + 20)
    d = (old + 1) - (old + 2)
    cr = c.replace_dict({(old+10).cache_key: (old+1), (old+20).cache_key: (old+2)})
    nose.tools.assert_is(cr, d)

    # test AST collapse
    s = claripy.SI(bits=32, stride=0, lower_bound=10, upper_bound=10)
    b = claripy.BVV(20, 32)

    sb = s+b
    nose.tools.assert_is_instance(sb.args[0], claripy.ast.Base)

    bb = b+b
    # this was broken previously -- it was checking if type(bb.args[0]) == A,
    # and it wasn't, but was instead a subclass. leaving this out for now
    # nose.tools.assert_not_is_instance(bb.args[0], claripy.ast.Base)

    # ss = s+s
    # (see above)
    # nose.tools.assert_not_is_instance(ss.args[0], claripy.ast.Base)

    sob = s|b
    # for now, this is collapsed. Presumably, Fish will make it not collapse at some point
    nose.tools.assert_is_instance(sob.args[0], claripy.ast.Base)

    # make sure the AST collapses for delayed ops like reversing
    rb = b.reversed
    #nose.tools.assert_is_instance(rb.args[0], claripy.ast.Base)
    # TODO: Properly delay reversing: should not be eager

    nose.tools.assert_is_not(rb, bb)
    nose.tools.assert_is(rb, rb)

    # test some alternate bvv creation methods
    nose.tools.assert_is(claripy.BVV('AAAA'), claripy.BVV(0x41414141, 32))
    nose.tools.assert_is(claripy.BVV('AAAA', 32), claripy.BVV(0x41414141, 32))
    nose.tools.assert_is(claripy.BVV('AB'), claripy.BVV(0x4142, 16))
    nose.tools.assert_is(claripy.BVV('AB', 16), claripy.BVV(0x4142, 16))
    nose.tools.assert_raises(claripy.errors.ClaripyValueError, claripy.BVV, 'AB', 8)

def test_cardinality():
    x = claripy.BVS('x', 32)
    y = claripy.BVS('y', 32, min=100, max=120)
    n = claripy.BVV(10, 32)
    m = claripy.BVV(20, 32)

    nose.tools.assert_equals(y.cardinality, 21)
    nose.tools.assert_equals(x.cardinality, 2**32)
    nose.tools.assert_equals(n.cardinality, 1)
    nose.tools.assert_equals(m.cardinality, 1)
    nose.tools.assert_equals(n.union(m).cardinality, 2)
    nose.tools.assert_equals(n.union(y).cardinality, 111)
    nose.tools.assert_equals(y.intersection(x).cardinality, 21)
    nose.tools.assert_equals(n.intersection(m).cardinality, 0)
    nose.tools.assert_equals(y.intersection(m).cardinality, 0)

    nose.tools.assert_true(n.singlevalued)
    nose.tools.assert_false(n.multivalued)

    nose.tools.assert_true(y.multivalued)
    nose.tools.assert_false(y.singlevalued)

    nose.tools.assert_false(x.singlevalued)
    nose.tools.assert_true(x.multivalued)

    nose.tools.assert_false(y.union(m).singlevalued)
    nose.tools.assert_true(y.union(m).multivalued)

    nose.tools.assert_false(y.intersection(m).singlevalued)
    nose.tools.assert_false(y.intersection(m).multivalued)

def test_if_stuff():
    x = claripy.BVS('x', 32)
    #y = claripy.BVS('y', 32)

    c = claripy.If(x > 10, (claripy.If(x > 10, x*3, x*2)), x*4) + 2
    cc = claripy.If(x > 10, x*3, x*4) + 2
    ccc = claripy.If(x > 10, x*3+2, x*4+2)
    cccc = x*claripy.If(x > 10, claripy.BVV(3, 32), claripy.BVV(4, 32)) + 2

    nose.tools.assert_is(c, cc)
    nose.tools.assert_is(c.ite_excavated, ccc)
    nose.tools.assert_is(ccc.ite_burrowed, cccc)

    i = c + c
    ii = claripy.If(x > 10, (x*3+2)+(x*3+2), (x*4+2)+(x*4+2))
    nose.tools.assert_is(i.ite_excavated, ii)

    cn = claripy.If(x <= 10, claripy.BVV(0x10, 32), 0x20)
    iii = c + cn
    iiii = claripy.If(x > 10, (x*3+2)+0x20, (x*4+2)+0x10)
    nose.tools.assert_is(iii.ite_excavated, iiii)

def test_ite():
    yield raw_ite, lambda: claripy.FullFrontend(claripy.backend_z3)
    yield raw_ite, lambda: claripy.HybridFrontend(claripy.backend_z3)
    yield raw_ite, lambda: claripy.CompositeFrontend(claripy.FullFrontend(claripy.backend_z3))

def raw_ite(solver_type):
    s = solver_type()
    x = claripy.BVS("x", 32)
    y = claripy.BVS("y", 32)
    z = claripy.BVS("z", 32)

    ite = claripy.ite_dict(x, {1:11, 2:22, 3:33, 4:44, 5:55, 6:66, 7:77, 8:88, 9:99}, claripy.BVV(0, 32))
    nose.tools.assert_equal(sorted(s.eval(ite, 100)), [ 0, 11, 22, 33, 44, 55, 66, 77, 88, 99 ] )

    ss = s.branch()
    ss.add(ite == 88)
    nose.tools.assert_equal(sorted(ss.eval(ite, 100)), [ 88 ] )
    nose.tools.assert_equal(sorted(ss.eval(x, 100)), [ 8 ] )

    ity = claripy.ite_dict(x, {1:11, 2:22, 3:y, 4:44, 5:55, 6:66, 7:77, 8:88, 9:99}, claripy.BVV(0, 32))
    ss = s.branch()
    ss.add(ity != 11)
    ss.add(ity != 22)
    ss.add(ity != 33)
    ss.add(ity != 44)
    ss.add(ity != 55)
    ss.add(ity != 66)
    ss.add(ity != 77)
    ss.add(ity != 88)
    ss.add(ity != 0)
    ss.add(y == 123)
    nose.tools.assert_equal(sorted(ss.eval(ity, 100)), [ 99, 123 ] )
    nose.tools.assert_equal(sorted(ss.eval(x, 100)), [ 3, 9 ] )
    nose.tools.assert_equal(sorted(ss.eval(y, 100)), [ 123 ] )

    itz = claripy.ite_cases([ (claripy.And(x == 10, y == 20), 33), (claripy.And(x==1, y==2), 3), (claripy.And(x==100, y==200), 333) ], claripy.BVV(0, 32))
    ss = s.branch()
    ss.add(z == itz)
    ss.add(itz != 0)
    nose.tools.assert_equal(ss.eval(y/x, 100), ( 2, ))
    nose.tools.assert_items_equal(sorted(ss.eval(x, 100)), ( 1, 10, 100 ))
    nose.tools.assert_items_equal(sorted(ss.eval(y, 100)), ( 2, 20, 200 ))

def test_bool():
    bc = claripy.backend_concrete

    a = claripy.And(*[False, False, True])
    nose.tools.assert_equal(bc.convert(a), False)
    a = claripy.And(*[True, True, True])
    nose.tools.assert_equal(bc.convert(a), True)

    o = claripy.Or(*[False, False, True])
    nose.tools.assert_equal(bc.convert(o), True)
    o = claripy.Or(*[False, False, False])
    nose.tools.assert_equal(bc.convert(o), False)

if __name__ == '__main__':
    test_smudging()
    test_expression()
    test_bool()
    test_ite()
    test_if_stuff()
