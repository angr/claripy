sat = 'sat'
unsat = 'unsat'

class Result(object):
    def __init__(self, satness, model):
        self.sat = satness
        self.model = model

class UnsatError(Exception):
    pass

