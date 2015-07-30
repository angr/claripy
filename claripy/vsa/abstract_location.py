from ..backend_object import BackendObject

class Segment(object):
    def __init__(self, offset, size=0):
        self.offset = offset
        self.size = size

    def __repr__(self):
        return "Seg (%s [ %d ])" % (hex(self.offset), self.size)

class AbstractLocation(BackendObject):
    def __init__(self, bbl_key, stmt_id, region_id, segment_list=None, region_offset=None, size=None):
        self._bbl_key = -1 if bbl_key is None else bbl_key
        self._stmt_id = -1 if stmt_id is None else stmt_id
        self._region_id = region_id
        self._segment_list = [ ] if not segment_list else segment_list[ :: ]

        if region_offset and size:
            self._add_segment(region_offset, size)

    def _add_segment(self, offset, size):
        segment_added = False

        last_pos = 0
        segment_end = offset + size

        for i, s in enumerate(self._segment_list):
            # Case 1
            s_end = s.offset + s.size

            if offset >= s.offset and segment_end <= s_end:
                # It has been covered
                return False

            if s.offset == offset or s.offset == (offset - 1) or s.offset == (offset + 1):
                s.offset = min(s.offset, offset)
                s.size = max(s_end, segment_end) - s.offset
                segment_added = True
                break

            # Case 2
            if s_end == segment_end or s_end == (segment_end - 1) or s_end == (segment_end + 1):
                s.offset = min(s.offset, offset)
                s.size = max(s_end, segment_end) - s.offset
                segment_added = True
                break

            if s.offset < offset:
                last_pos = i + 1

        if not segment_added:
            # We create a new segment and add it to the list
            s = Segment(offset, size)
            self._segment_list.insert(last_pos, s)

        # Check for possible merges
        i = 0
        while i < len(self._segment_list) - 1:
            s = self._segment_list[i]
            t = self._segment_list[i + 1]

            if s.offset + s.size >= t.offset:
                # They should be merged!
                new_s = Segment(s.offset, max(s.offset + s.size, t.offset + t.size) - s.offset)
                self._segment_list[ i : i + 2 ] = [ new_s ]

            else:
                i += 1

        return True

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
    def segments(self):
        return self._segment_list

    def update(self, region_offset, size):
        updated = self._add_segment(region_offset, size)

        return updated

    def copy(self):
        return AbstractLocation(self._bbl_key, self._stmt_id, self._region_id,
                                self._segment_list)

    def merge(self, other):
        merged = False

        for s in other._segment_list:
            merged |= self.update(s.offset, s.size)

        return merged

    def __contains__(self, offset):
        for s in self._segment_list:
            if s.offset <= offset and s.offset + s.size > offset:
                return True

            if s.offset > offset:
                break

        return False

    def __repr__(self):
        return '(%xh, %d) %s' % (
            (self.basicblock_key if self.basicblock_key is not None else -1),
            (self.statement_id if self.statement_id is not None else -1),
            self._segment_list
        )
