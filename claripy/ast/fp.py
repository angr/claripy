from .bits import Bits

class FP(Bits):
    def to_fp(self, rm, sort):
        if rm is None:
            rm = RM.default()

        return self._claripy.fpToFP(rm, self, sort)

    def raw_to_fp(self):
        return self

    def to_bv(self):
        return self._claripy.fpToIEEEBV(self)

def FPI(claripy, model, **kwargs):
    kwargs['length'] = model.sort.length
    return FP(claripy, 'I', (model,), **kwargs)

from ..fp import RM
