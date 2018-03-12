from .backend_object import BackendObject

# TODO : figure out what is this...
class StringV(BackendObject):
    def __init__(self, value):
        self.value = value
    
def Substr(f, t, o):
    """
    Create a concrete version of the substring
    :param f : starting index of the substring
    :param t : last index of the substring
    :o : Argument of the AST 
    """
    if f == t:
        new_value = o.args[0][f]
    else:
        new_value = o.args[0][f:t]
    return StringV(new_value)