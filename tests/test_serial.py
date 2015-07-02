import claripy
import ana
import nose
import pickle
import tempfile

import logging
l = logging.getLogger('claripy.test.serial')

def test_pickle():
    clrp = claripy.Claripies['SerialZ3']
    bz = clrp.backend_of_type(claripy.backends.BackendZ3)

    a = clrp.BitVecVal(0, 32)
    b = clrp.BitVec('x', 32, explicit_name=True)

    c = a+b
    nose.tools.assert_equal(c.resolved_with(bz).__module__, 'z3')
    nose.tools.assert_equal(str(c.resolved_with(bz)), '0 + x')

    c_copy = pickle.loads(pickle.dumps(c, -1))
    nose.tools.assert_equal(c_copy.resolved_with(bz).__module__, 'z3')
    nose.tools.assert_equal(str(c_copy.resolved_with(bz)), '0 + x')

def test_datalayer():
    l.info("Running test_datalayer")

    clrp = claripy.Claripies['SerialZ3']
    pickle_dir = tempfile.mkdtemp()
    ana.set_dl(pickle_dir=pickle_dir)
    l.debug("Pickling to %s",pickle_dir)

    a = clrp.BitVecVal(0, 32)
    b = clrp.BitVec("x", 32)
    c = a + b
    d = a+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b+b

    l.debug("Storing!")
    a.ana_store()
    c_info = c.ana_store()
    d_info = d.ana_store()

    l.debug("Loading!")
    ana.set_dl(pickle_dir=pickle_dir)
    #nose.tools.assert_equal(len(clrp.dl._cache), 0)

    cc = claripy.BV.ana_load(c_info)
    nose.tools.assert_equal(str(cc), str(c))
    cd = claripy.BV.ana_load(d_info)
    nose.tools.assert_equal(str(cd), str(d))

    l.debug("Time to test some solvers!")
    s = clrp.solver()
    x = clrp.BitVec("x", 32)
    s.add(x == 3)
    s.finalize()
    ss = claripy.solvers.Solver.ana_load(s.ana_store())
    nose.tools.assert_equal(str(s.constraints), str(ss.constraints))
    nose.tools.assert_equal(str(s.variables), str(ss.variables))

    s = clrp.composite_solver()
    x = clrp.BitVec("x", 32)
    s.add(x == 3)
    s.finalize()
    ss = claripy.solvers.CompositeSolver.ana_load(s.ana_store())
    old_constraint_sets = [[hash(j) for j in k.constraints] for k in s._solver_list]
    new_constraint_sets = [[hash(j) for j in k.constraints] for k in ss._solver_list]
    nose.tools.assert_items_equal(old_constraint_sets, new_constraint_sets)
    nose.tools.assert_equal(str(s.variables), str(ss.variables))

if __name__ == '__main__':
    test_pickle()
    test_datalayer()
