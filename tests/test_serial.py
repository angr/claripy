import claripy
import ana
import nose
import pickle
import tempfile

import logging
l = logging.getLogger('claripy.test.serial')

def test_pickle_ast():
    bz = claripy.backends.z3

    a = claripy.BVV(1, 32)
    b = claripy.BVS('x', 32, explicit_name=True)

    c = a+b
    nose.tools.assert_equal(bz.convert(c).__module__, 'z3')
    nose.tools.assert_equal(str(bz.convert(c)), '1 + x')

    c_copy = pickle.loads(pickle.dumps(c, -1))
    nose.tools.assert_equal(bz.convert(c_copy).__module__, 'z3')
    nose.tools.assert_equal(str(bz.convert(c_copy)), '1 + x')

def test_pickle_frontend():
    s = claripy.Solver()
    x = claripy.BVS('x', 32)

    s.add(x == 1)
    assert s.eval(x, 10), (1,)

    ss = pickle.dumps(s)
    del s
    import gc
    gc.collect()

    s = pickle.loads(ss)
    assert s.eval(x, 10), (1,)

def test_datalayer():
    l.info("Running test_datalayer")

    pickle_dir = tempfile.mkdtemp()
    ana.set_dl(ana.DirDataLayer(pickle_dir))
    l.debug("Pickling to %s",pickle_dir)

    a = claripy.BVV(1, 32)
    b = claripy.BVS("x", 32)
    c = a + b
    d = a+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b

    l.debug("Storing!")
    a.ana_store()
    c_info = c.ana_store()
    d_info = d.ana_store()

    l.debug("Loading!")
    ana.set_dl(ana.DirDataLayer(pickle_dir))
    #nose.tools.assert_equal(len(claripy.dl._cache), 0)

    cc = claripy.ast.BV.ana_load(c_info)
    nose.tools.assert_equal(str(cc), str(c))
    cd = claripy.ast.BV.ana_load(d_info)
    nose.tools.assert_equal(str(cd), str(d))

    l.debug("Time to test some solvers!")
    s = claripy.Solver()
    x = claripy.BVS("x", 32)
    s.add(x == 3)
    s.finalize()
    ss = claripy.Solver.ana_load(s.ana_store())
    nose.tools.assert_equal(str(s.constraints), str(ss.constraints))
    nose.tools.assert_equal(str(s.variables), str(ss.variables))

    s = claripy.SolverComposite()
    x = claripy.BVS("x", 32)
    s.add(x == 3)
    s.finalize()
    ss = claripy.SolverComposite.ana_load(s.ana_store())
    old_constraint_sets = [[hash(j) for j in k.constraints] for k in s._solver_list]
    new_constraint_sets = [[hash(j) for j in k.constraints] for k in ss._solver_list]
    nose.tools.assert_items_equal(old_constraint_sets, new_constraint_sets)
    nose.tools.assert_equal(str(s.variables), str(ss.variables))

if __name__ == '__main__':
    test_pickle_ast()
    test_pickle_frontend()
    test_datalayer()
