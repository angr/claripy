class Storable(object):
    __slots__ = [ '_claripy', '_uuid', '_stored' ]

    def __init__(self, claripy, uuid=None, stored=None):
        self._claripy = claripy
        self._uuid = uuid
        self._stored = False if stored is None else stored

    @property
    def uuid(self):
        if self._uuid is not None:
            return self._uuid
        else:
            return self._claripy.datalayer.make_uuid(self)

    def __getstate__(self):
        if self._uuid is not None:
            if not self._stored:
                self._claripy.datalayer.store_state(self._uuid, self._claripy_getstate())
                self._stored = True
            return self._uuid
        else:
            return self._claripy_getstate()

    def __setstate__(self, s):
        if type(s) is str:
            Storable.__init__(self, get_claripy(), uuid=s, stored=True)
            s = self._claripy.datalayer.load_state(self._uuid)
        else:
            Storable.__init__(self, get_claripy(), uuid=None, stored=False)

        self._claripy_setstate(s)

    def _claripy_getstate(self):
        raise NotImplementedError()

    def _claripy_setstate(self, s):
        raise NotImplementedError()

    def store(self):
        '''
        Assigns a UUID to the storable and stores the actual data.
        '''
        u = self.uuid
        if not self._stored:
            self._claripy.datalayer.store_state(self._uuid, self._claripy_getstate())
            self._stored = True
        return u

    @classmethod
    def load(cls, uuid):
        self = cls.__new__(cls)
        self.__setstate__(uuid)
        return self

from . import get_claripy
