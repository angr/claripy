sat = 'sat'
unsat = 'unsat'

import copy

class Result(object):
    def __init__(self, satness, model, backend_model=None):
        self.sat = satness
        self.model = model
        self.backend_model = backend_model

    def branch(self):
        return Result(self.sat, copy.copy(self.model), backend_model=self.backend_model)

class UnsatError(Exception):
    pass

