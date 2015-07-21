import itertools

from . import celeryconfig

import celery
from celery.contrib import rdb
import pymongo

app = celery.Celery('tasks', broker='amqp://guest@localhost//', backend='mongodb://localhost/')
app.config_from_object(celeryconfig)
z3 = None
mongo = None

@celery.signals.celeryd_after_setup.connect
def init_z3_and_conns(sender, instance, **kwargs):
    global z3, mongo
    z3 = claripy.backends.BackendZ3()
    z3.set_claripy_object(claripy.Claripies['SerialZ3'])
    mongo = pymongo.MongoClient()['lemma_cache']

def canonicalize_all(exprs):
    known_vars = {}
    counter = itertools.count()
    return [expr.canonicalized(existing_vars=known_vars, counter=counter)[1] for expr in exprs]

@app.task
def check(constraints):
    global z3

    independent = Solver.independent_constraints(constraints)
    # TODO: deal with different *orders* of constraints
    parts = {}
    for (_, cset) in independent:
        all_canonicalized = canonicalize_all(cset)
        # note: the `sorted` does not fix the above TODO because it
        # does not account for different orderings in variable
        # renamings
        parts[tuple(sorted(e.ana_uuid for e in all_canonicalized))] = all_canonicalized

    for doc in mongo['check'].find({'$or': [{'uuids': uu} for uu in parts]}):
        print "lemma cache find, result for %r is %s" % (doc['uuids'], doc['sat'])
        if doc['sat']:
            # this part is sat, don't need to check it again
            del parts[doc['uuids']]
        else:
            # this part is unsat, so as a whole, constraints must be unsat
            return False

    s = z3.solver()

    for uuids, exprs in parts.items():
        sat = z3.check(s, extra_constraints=exprs)
        mongo['check'].insert_one({'uuids': uuids, 'sat': sat})
        if not sat:
            return False

    return True

@app.task
def eval(constraints, expr, n):
    global z3
    s = z3.solver()
    z3.add(s, constraints)
    return z3.eval(s, expr, n)

@app.task
def results(constraints):
    # TODO: implement model
    return Result(check(constraints), {})
    # global z3
    # s = z3.solver()
    # z3.add(s, constraints)
    # return z3.results(s)

@app.task
def min(constraints, expr):
    global z3
    s = z3.solver()
    z3.add(s, constraints)
    return z3.min(s, expr)

@app.task
def max(constraints, expr):
    global z3
    s = z3.solver()
    z3.add(s, constraints)
    return z3.max(s, expr)


import claripy
from claripy.solvers import Solver
from ..result import Result
from ..ast import base
base.WORKER = False
