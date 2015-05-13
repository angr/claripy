from .bits import Bits

class FP(Bits):
    pass

def FPI(claripy, model, **kwargs):
    return FP(claripy, 'I', (model,), **kwargs)
