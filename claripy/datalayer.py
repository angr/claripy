import os
import cPickle as pickle

class DataLayer:
    '''
    The DataLayer handles storing and retrieving UUID-identified objects
    to/from a central store.
    '''

    def __init__(self, pickle_dir=None):
        self._dir = pickle_dir

        if pickle_dir is None:
            raise TypeError("Invalid args to DataLayer!")

    def store(self, uuid, thing):
        if self._dir is not None:
            pickle.dump(thing, open(os.path.join(self._dir, str(uuid)+'.p'), 'w'))

    def load(self, uuid):
        if self._dir is not None:
            pickle.load(open(os.path.join(self._dir, str(uuid)+'.p'), 'w'))
