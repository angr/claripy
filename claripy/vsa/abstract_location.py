class AbstractLocation(object):
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

    def update(self, addr, size):
        pass