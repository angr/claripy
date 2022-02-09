__all__ = ["AnnotationSPAV"]

from .claricpp import *
from .annotation import *
from functools import lru_cache

# TODO: deal with destruction / freeing memory
# TODO: slots!


class AnnotationSPAV:
    """
    Wraps a ClaricppSPAV
    """

    _empty_raw = claricpp.claricpp_annotation_create_empty_spav()

    def __init__(self, data=None):
        """
        Convert a list of Annotations to an AnnotationSPAV or wrap a Claricpp SPAV
        """
        if data is None:
            self._spav = self._empty_raw
        elif type(data) is List:
            n = len(data)
            if n == 0:
                self._spav = self._empty_raw
            else:
                self._spav = claricpp.claricpp_annotation_create_spav(data, n)
        else:
            self._spav = data

    @lru_cache(maxsize=None)
    def __getitem__(self, index: int) -> Annotation:
        return Annotation(claricpp.claricpp_annotation_spav_get(self._spav, index))

    @lru_cache(maxsize=None)
    def __len__(self) -> int:
        return claricpp.claricpp_annotation_spav_len(self._spav)

    @property
    @lru_cache(maxsize=None)
    def _as_c_arr(self):
        """
        Convert self._spav to an array of annotations
        """
        return claricpp.claricpp_annotation_spav_to_array(self._spav)

    @lru_cache(maxsize=None)
    def as_list(self) -> list[Annotation]:
        ret = []
        arr = self._as_c_arr
        for index in range(arr.len):
            ret.append(Annotation(arr.arr[index]))
        return ret

    @property
    @lru_cache(maxsize=None)
    def raw(self):
        """
        Get the raw spav self holds
        Warning: Do not call this function unless you know what you are doing!
        """
        return self._spav
