__all__ = ["Annotation", "SimplificationAvoidanceAnnotation"]

from .claricpp import *
from functools import lru_cache

# TODO: deal with destruction / freeing memory
# TODO: slots!


class Annotation:
    """
    Wraps a Claricpp Annotation
    """

    def __init__(self, raw):
        if raw is None:
            self._raw = claricpp.claricpp_annotation_new_base()
        else:
            self._raw = raw

    @property
    @lru_cache(maxsize=None)
    def eliminatable(self):
        return claricpp.claricpp_annotation_eliminatable()

    @property
    @lru_cache(maxsize=None)
    def relocatable(self):
        return claricpp.claricpp_annotation_relocatable()



class SimplificationAvoidanceAnnotation(Annotation):
    """
    Wraps a Claricpp Simplification Avoidance Annotation
    """

    def __init__(self, raw):
        if raw is None:
            raw = claricpp.claricpp_annotation_new_simplification_avoidance()
        super().__init__(raw)
