import os
import cPickle as pickle
import weakref
import uuid as uuid_module

import logging
l = logging.getLogger("claripy.datalayer")

# This is the global datalayer.
dl = None

def init(*args, **kwargs):
    '''
    Initializes the global DataLayer.
    '''
    global dl
    dl = DataLayer(*args, **kwargs)

class DataLayer:
    '''
    The DataLayer handles storing and retrieving UUID-identified objects
    to/from a central store.
    '''

    def __init__(self, pickle_dir=None):
        self._cache = weakref.WeakValueDictionary()
        self._dir = pickle_dir

        if pickle_dir is not None:
            self._store_type = 'pickle'
        else:
            self._cache = { }
            self._store_type = 'dict'

    def store_expression(self, e):
        if e._stored:
            l.debug("%s is already stored", e)
            if e._uuid not in self._cache:
                l.warning("%s is already stored but UUID %s is not in cache", e, e._uuid)
                self._cache[e._uuid] = e
            return

        uuid = str(uuid_module.uuid4())
        l.debug("storing expression %s with uuid %s", e, uuid)
        self._store(uuid, e)
        e._stored = True
        e._uuid = uuid

    def load_expression(self, uuid):
        e = self._load(uuid)
        l.debug("loaded expression %s with uuid %s", e, uuid)
        e._uuid = uuid
        e._stored = True
        return e

    def _store(self, uuid, thing):
        self._cache[uuid] = thing

        if self._store_type == 'pickle':
            pickle.dump(thing, open(os.path.join(self._dir, str(uuid)+'.p'), 'w'), -1)
        elif self._store_type == 'dict':
            return

    def _load(self, uuid):
        if uuid in self._cache:
            return self._cache[uuid]

        if self._store_type == 'pickle':
            return pickle.load(open(os.path.join(self._dir, str(uuid)+'.p')))
        elif self._store_type == 'dict':
            # should never be reached due to the cache check above, actually
            return self._cache[uuid]
