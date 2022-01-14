__all__ = ["Annotation", "SimplificationAvoidanceAnnotation"]

from claricpp import *

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


class SimplificationAvoidanceAnnotation(Annotation):
    """
    Wraps a Claricpp Simplification Avoidance Annotation
    """

    def __init__(self, raw):
        if raw is None:
            raw = claricpp.claricpp_annotation_new_simplification_avoidance()
        super().__init__(raw)
