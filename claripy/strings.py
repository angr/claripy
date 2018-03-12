from .backend_object import BackendObject

# TODO : figure out what is this...
class StringV(BackendObject):
    def __init__(self, value):
        self.value = value

    def __repr__(self):
        return 'StringV(%s)' % (self.value)
    
def Substr(start_idx, end_idx, initial_string):
    """
    Create a concrete version of the substring
    :param start_idx : starting index of the substring
    :param end_idx : last index of the substring
    :param initial_string : Argument of the AST 

    :return : a concrete version of the substring
    """
    if start_idx == end_idx:
        new_value = initial_string.value[start_idx]
    else:
        new_value = initial_string.value[start_idx:end_idx]
    return StringV(new_value)


def Replace(initial_string, pattern_to_be_replaced, replacement_pattern):
    """
    Create a concrete version of the replaced string
    (replace ONLY th efirst occurrence of the pattern)
    :param initial_string : string in which the pattern needs to be replaced
    :param pattern_to_be_replaced : substring that has to be replaced inside initial_string 
    :param replacement_poattern : pattern that has to be inserted in initial_string t replace
                                  pattern_to_be_replaced
    
    :return : a concrete representation of the replaced string
    """
    new_value = initial_string.value.replace(pattern_to_be_replaced.value, 
                                             replacement_pattern.value,
                                             1)
    return StringV(new_value)

    # return StringV(new_value)