import os
import cPickle as pickle
import uuid as uuid_module

import logging
l = logging.getLogger("claripy.datalayer")

class DataLayer:
    '''
    The DataLayer handles storing and retrieving UUID-identified objects
    to/from a central store.
    '''

    def __init__(self, claripy, pickle_dir=None):
        self._hash_cache = { }
        self._claripy = claripy

        if pickle_dir is not None:
            self._store_type = 'pickle'
            self._dir = pickle_dir

            if not os.path.exists(self._dir):
                l.warning("Directory '%s' doesn't exit. Creating.", self._dir)
                os.makedirs(self._dir)
        else:
            self._store_type = 'dict'
            self._state_store = { }

    @staticmethod
    def make_uuid(e):
        e._uuid = str(uuid_module.uuid4())
        return e._uuid

    def make_expression(self, model, variables=None, symbolic=False, objects=None, simplified=False):
        h = hash(model)
        if h in self._hash_cache:
            return self._hash_cache[h]

        e = E(self._claripy, model=model, variables=set() if variables is None else variables, objects=objects, symbolic=symbolic, simplified=simplified)
        self._hash_cache[h] = e
        return e

    def store_state(self, uuid, s):
        p = pickle.dumps(s, protocol=-1)
        if self._store_type == 'pickle':
            open(os.path.join(self._dir, str(uuid)+'.p'), 'w').write(p)
        elif self._store_type == 'dict':
            self._state_store[uuid] = p

    def load_state(self, uuid):
        if self._store_type == 'pickle':
            p = open(os.path.join(self._dir, str(uuid)+'.p')).read()
        elif self._store_type == 'dict':
            p = self._state_store[uuid]

        return pickle.loads(p)

from .expression import E
