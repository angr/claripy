from .backend_object import BackendObject

# TODO : figure out what is this...
class StringV(BackendObject):
    def __init__(self, value):
        self.value = value
    
def Substr(f, t, o):
    if f == t:
        new_value = o.args[0][f]
    else:
        new_value = o.args[0][f:t]
    return StringV(new_value)