from ..backend import BackendObject

class AbstractLocation(BackendObject):
    def __init__(self, bbl_key, stmt_id, region_id, region_offset, size):
        self._bbl_key = bbl_key
        self._stmt_id = stmt_id
        self._region_id = region_id
        self._region_offset = region_offset
        self._size = size

    @property
    def basicblock_key(self):
        return self._bbl_key

    @property
    def statement_id(self):
        return self._stmt_id

    @property
    def region(self):
        return self._region_id

    @property
    def offset(self):
        return self._region_offset

    @property
    def size(self):
        return self._size

    def update(self, region_offset, size):
        # TODO: We can improve this method
        updated = False

        if region_offset >= self.offset:
            new_size = (region_offset + size) - self.offset
            if self._size <  new_size:
                updated = True
                self._size = new_size
        elif region_offset <= self.offset:
            updated = True
            self._size = max(self._size - region_offset, size - region_offset)
            self._region_offset = region_offset

        return updated

    def copy(self):
        return AbstractLocation(self._bbl_key, self._stmt_id, self._region_id,
                                self._region_offset, self._size)

    def __repr__(self):
        return '[%xh, %d] %xh, %d bytes' % (self.basicblock_key, self.statement_id, self.offset, self.size)
