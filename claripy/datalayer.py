import os
import cPickle as pickle
import weakref
import uuid as uuid_module

import logging
l = logging.getLogger("claripy.datalayer")

class DataLayer:
    '''
    The DataLayer handles storing and retrieving UUID-identified objects
    to/from a central store.
    '''

    def __init__(self, claripy, pickle_dir=None):
        self._uuid_cache = weakref.WeakValueDictionary()
        self._hash_cache = weakref.WeakValueDictionary()
        self._dir = pickle_dir
        self._claripy = claripy

        if pickle_dir is not None:
            self._store_type = 'pickle'
        else:
            self._uuid_cache = { }
            self._store_type = 'dict'

    @staticmethod
    def make_uuid(e):
        e._uuid = str(uuid_module.uuid4())
        return e._uuid

    def store_expression(self, e):
        if e._stored:
            l.debug("%s is already stored", e)
            if e._uuid not in self._uuid_cache:
                l.warning("%s is already stored but UUID %s is not in cache", e, e._uuid)
                self._uuid_cache[e._uuid] = e
            return

        self.make_uuid(e)
        l.debug("storing expression %s with uuid %s", e, e.uuid)
        self._store(e.uuid, e)
        e._stored = True

    def load_expression(self, uuid):
        e = self._load(uuid)
        l.debug("loaded expression %s with uuid %s", e, uuid)
        e._uuid = uuid
        e._stored = True
        return e

    def make_expression(self, model, variables=None, symbolic=False, objects=None, length=-1, simplified=False):
        h = hash(model)
        if h in self._hash_cache:
            return self._hash_cache[h]

        e = E(self._claripy, model=model, variables=set() if variables is None else variables, objects=objects, symbolic=symbolic, length=length, simplified=simplified)
        self._hash_cache[h] = e
        return e

    def _store(self, uuid, thing):
        self._uuid_cache[uuid] = thing

        if self._store_type == 'pickle':
            pickle.dump(thing, open(os.path.join(self._dir, str(uuid)+'.p'), 'w'), -1)
        elif self._store_type == 'dict':
            return

    def _load(self, uuid):
        if uuid in self._uuid_cache:
            return self._uuid_cache[uuid]

        if self._store_type == 'pickle':
            return pickle.load(open(os.path.join(self._dir, str(uuid)+'.p')))
        elif self._store_type == 'dict':
            # should never be reached due to the cache check above, actually
            return self._uuid_cache[uuid]

from .expression import E
