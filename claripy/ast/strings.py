from .bits import Bits
from ..ast.base import _make_name

from .. import operations
from .bool import Bool


class String(Bits):
    def __getitem__(self, rng):
        if type(rng) is slice:
            left = rng.start if rng.start is not None else len(self)-1
            right = rng.stop if rng.stop is not None else 0
            if left < 0:
                left = len(self) + left
            if right < 0:
                right = len(self) + right
            return Extract(left, right, self)
        else:
            return Extract(int(rng), int(rng), self)

def StringS(name, size, uninitialized=False, explicit_name=False, **kwargs):
    n = _make_name(name, size, False if explicit_name is None else explicit_name)
    result = String("StringS", (n, uninitialized), length=size, symbolic=True, eager_backends=None, uninitialized=uninitialized, **kwargs)
    return result

def StringV(value, **kwargs):
    result = String("StringV", (value, len(value)), length=len(value), **kwargs)
    return result

# called after simplifaction
Concat = operations.op('Concat', String, String, calc_length=operations.concat_length_calc, bound=False)
Extract = operations.op('Extract', ((int, long), (int, long), String),
                        String, extra_check=operations.extract_check,
                        calc_length=operations.extract_length_calc, bound=False)

# called before simplifaction
String.__add__ = operations.op('Concat', (String, String), String, calc_length=operations.concat_length_calc, bound=False)
String.__eq__ = operations.op('__eq__', (String, String), Bool, extra_check=operations.length_same_check)
String.Extract = staticmethod(operations.op('Extract', ((int, long), (int, long), String), String, extra_check=operations.extract_check, calc_length=operations.extract_length_calc, bound=False))
