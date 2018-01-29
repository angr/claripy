from .bits import Bits
from ..ast.base import _make_name

from .. import operations


class String(Bits):
    def casa(self):
        pass

def StringSym(name, size, uninitialized=False, explicit_name=False, **kwargs):
    n = _make_name(name, size, False if explicit_name is None else explicit_name)
    result = String("StringSym", (n, uninitialized), length=size, symbolic=True, eager_backends=None, uninitialized=uninitialized, **kwargs)
    return result

def StringVal(value, **kwargs):
    result = String("StringVal", (value, len(value)), length=len(value), **kwargs)
    return result

# called after simplifaction
Concat = operations.op('Concat', String, String, calc_length=operations.concat_length_calc, bound=False)

# called before simplifaction
String.__add__ = operations.op('Concat', (String, String), String, calc_length=operations.concat_length_calc, bound=False)
