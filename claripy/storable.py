class Storable(object):
    __slots__ = [ '_claripy', '_uuid' ]

    def __init__(self, claripy, uuid=None):
        self._claripy = claripy
        self._uuid = uuid

    def _load(self):
        raise NotImplementedError()

    @property
    def uuid(self):
        if self._uuid is not None:
            return self._uuid
        else:
            return self._claripy.dl.make_uuid(self)
