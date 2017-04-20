#
# Some built-in annotations
#

class SimplificationAvoidanceAnnotation(object):
    pass

class VariableAnnotation(object):
    def __init__(self, extra_variables):
        self.extra_variables = extra_variables
