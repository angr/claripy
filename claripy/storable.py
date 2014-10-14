class Storable(object):
    __slots__ = [ '_claripy', '_uuid', '_stored' ]

    def __init__(self, claripy, uuid=None, stored=None):
        self._claripy = claripy
        self._uuid = uuid
        self._stored = False if stored is None else stored

    def _storable_kwargs(self):
        return {
            'uuid': self._uuid,
            'stored': self._stored
        }

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
            return self._claripy.name, self._uuid
        else:
            return self._claripy.name, self._claripy_getstate()

    def __setstate__(self, s):
        clrp_name, s = s
        clrp = Claripies[clrp_name]

        if type(s) is str:
            Storable.__init__(self, clrp, uuid=s, stored=True)
            s = self._claripy.datalayer.load_state(self._uuid)
        else:
            Storable.__init__(self, clrp, uuid=None, stored=False)

        self._claripy_setstate(s)

    def _claripy_getstate(self):
        raise NotImplementedError()

    def _claripy_setstate(self, s):
        raise NotImplementedError()

    def store(self):
        '''
        Assigns a UUID to the storable and stores the actual data.
        '''
        u = self.uuid #pylint:disable=unused-variable
        return self.__getstate__()

    @classmethod
    def load(cls, s):
        self = cls.__new__(cls)
        self.__setstate__(s)
        return self

from . import Claripies
