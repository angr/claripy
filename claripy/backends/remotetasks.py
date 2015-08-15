import cPickle as pickle
import functools
import itertools
import logging
import time
l = logging.getLogger('claripy.backends.remotetasks')

from . import celeryconfig

import celery
from celery.contrib import rdb
import pymongo
import bson

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

def flip_dict(d):
    return {val: key for (key, val) in d.items()}

def canonicalize_all(exprs):
    known_vars = {}
    counter = itertools.count()
    return known_vars, [expr.canonicalized(existing_vars=known_vars, counter=counter)[1] for expr in exprs]

def split_and_canonicalize(constraints):
    independent = Solver.independent_constraints(constraints)
    # TODO: deal with different *orders* of constraints
    parts = {}
    for _, cset in independent:
        mapping, all_canonicalized = canonicalize_all(cset)
        # note: the `sorted` does not fix the above TODO because it
        # does not account for different orderings in variable
        # renamings
        parts[tuple(sorted(str(e._hash) for e in all_canonicalized))] = (mapping, all_canonicalized)
    return parts

@app.task
def check(constraints):
    return results(constraints).sat
    # global z3

    # parts = split_and_canonicalize(constraints)
    # all_uuids = sorted(uu for uuids in parts for uu in uuids)

    # if mongo['results'].find({'uuids': {'$in': all_uuids}, 'sat': False}).limit(1).count(with_limit_and_skip=True) > 0:
    #     # this means a constraint set consisting of a subset of the
    #     # uuids is unsat, meaning all the uuids together must also be
    #     # unsat
    #     return False

    # for doc in mongo['results'].find({'$or': [{'uuids': uu} for uu in parts]}):
    #     l.info("lemma cache find, result for %r is %s", doc['uuids'], doc['sat'])
    #     if doc['sat']:
    #         # this part is sat, don't need to check it again
    #         del parts[tuple(doc['uuids'])]
    #     else:
    #         # this part is unsat, so as a whole, constraints must be unsat
    #         return False

    # s = z3.solver()

    # for uuids, (_, exprs) in parts.items():
    #     sat = z3.check(s, extra_constraints=exprs)
    #     mongo['results'].insert_one({'uuids': uuids, 'sat': sat, 'model': None})
    #     if not sat:
    #         return False

    # return True

@app.task
def eval(constraints, expr, n):
    global z3
    s = z3.solver()
    z3.add(s, constraints)
    return z3.eval(s, expr, n)

def rename_model(mapping, model, transform=lambda x: x):
    print model
    return {
        # if the name isn't in the model, then it's a "don't care",
        # i.e., it can hold any value
        orig_var_name: transform(model[generic_var.args[0]]) if generic_var.args[0] in model else generic_var._claripy.BVV(0, sz)
        for ((orig_var_name, sz), generic_var)
        in mapping.items()
    }

def report_sat(f):
    @functools.wraps(f)
    def wrapped(constraints):
        result = f(constraints)
        l.warning("result.sat = %s", result.sat)
        return result
    return wrapped

def mongo_superset(s):
    # this is probably highly inefficient...
    return {'$not': {'$elemMatch': {'$nin': s}}}

@app.task
@report_sat
def results(constraints):
    global z3

    with open('./foo.p', 'wb') as f:
        pickle.dump(constraints, f)

    if len(constraints) == 0:
        return Result(True, {})

    before = time.time()

    model = {}
    parts = split_and_canonicalize(constraints)
    all_uuids = sorted(uu for uuids in parts for uu in uuids)

    print "before mongo stuff took %f" % (time.time() - before)

    if mongo['results'].find({'uuids': mongo_superset(all_uuids), 'sat': False}).limit(1).count(with_limit_and_skip=True) > 0:
        # this means a constraint set consisting of a subset of the
        # uuids is unsat, meaning all the uuids together must also be
        # unsat
        print "found unsat $in"
        return Result(False, {})

    print "whole pre-solve took %f" % (time.time() - before)

    # for doc in mongo['results'].find({'$or': [{'uuids': uu} for uu in parts]}):
    #     l.info("lemma cache find for %r, sat is %s and model is %s", doc['uuids'], doc['sat'], doc['model'])
    #     # if doc['sat']:
    #     #     if doc['model'] is not None:
    #     #         mapping, _ = parts[tuple(doc['uuids'])]
    #     #         model.update(rename_model(mapping, doc['model'], transform=pickle.loads))
    #     #         del parts[tuple(doc['uuids'])]
    #     if not doc['sat']:
    #         return Result(False, {})

    s = z3.solver()

    for uuids, (mapping, exprs) in parts.items():
        if all(e.is_true() for e in exprs):
            continue

        result = z3.results(s, extra_constraints=exprs, generic_model=True)
        doc = {
            'uuids': uuids,
            'sat': result.sat,
            'model': None,
        }
        if result.sat:
            doc['model'] = {name: bson.binary.Binary(pickle.dumps(val, protocol=pickle.HIGHEST_PROTOCOL))
                            for (name, val) in result.model.items()}
            try:
                model.update(rename_model(mapping, result.model))
            except KeyError:
                rdb.set_trace()

        mongo['results'].replace_one({'uuids': uuids}, doc, upsert=True)

        if not result.sat:
            return Result(False, {})

    return Result(True, model)

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
from ..solvers import Solver
from ..result import Result
from ..ast import base
