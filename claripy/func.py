import re
from .backend_object import BackendObject
from .bv import BVV


class FuncV(BackendObject):
    def __init__(self, func_name, *args):
        self.args = args
        self.func_name = func_name

    def __repr__(self):
        repr = self.func_name + '('

        for i in range(len(self.args)):
            arg = self.args[i]
            repr += arg.__repr
            if i != len(self.args):
                repr += ', '

        repr += ')'
        return repr

def FuncDecl(func_name, *args):
    return FuncV(func_name, *args)