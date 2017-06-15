import weakref
from ast.structure import canonical_structure
from . import UnsatError
import logging


l = logging.getLogger("claripy.solver_cache")

class CanonicalCache(dict):
    """
    Represents a cache of solutions to various canonicalized AST structures.
    Maps the hash of a canonicalized AST structure to a dictionary that represents
    a sat model (variable NAME -> value) OR False, which implies unsat. Use as you
    would a dictionary, even with non-canonicalized ASTs or ASTStructures (will
    automatically canonicalize).
    """
    def __init__(self):
        self.unsats = {}
        self.models = {}

    def __getitem__(self, key):
        canonical = hash(canonical_structure(key))
        return super(CanonicalCache, self).__getitem__(canonical)

    def __setitem__(self, key, value):
        canonical = hash(canonical_structure(key))
        if value is False:
            self.unsats[canonical] = False
        elif isinstance(value, dict):
            self.models[canonical] = value
        else:
            raise TypeError(type(value))
        return super(CanonicalCache, self).__setitem__(canonical, value)

    def add_unsat(self, key):
        self[key] = False

    def add_model(self, key, model):
        self[key] = model

    def is_unsat(self, key):
        return self[key] is False

    def get_model(self, key):
        model = self[key]
        if model is False:
            raise UnsatError("key is unsat")
        return model


global_solution_cache = CanonicalCache()
