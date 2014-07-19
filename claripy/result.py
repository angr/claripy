sat = 'sat'
unsat = 'unsat'

import copy

class Result(object):
    def __init__(self, satness, model):
        self.sat = satness
        self.model = model

    def branch(self):
        return Result(self.sat, copy.copy(self.model))

class UnsatError(Exception):
    pass

