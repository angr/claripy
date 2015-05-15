from .base import Base
from ..operations import op

class Bool(Base):
    @staticmethod
    def _from_bool(clrp, like, val):
        return BoolI(clrp, val)

    def is_true(self):
        '''
        Returns True if 'self' can be easily determined to be True.
        Otherwise, return False. Note that the AST *might* still be True (i.e.,
        if it were simplified via Z3), but it's hard to quickly tell that.
        '''
        return self._claripy.is_true(self)

    def is_false(self):
        '''
        Returns True if 'self' can be easily determined to be False.
        Otherwise, return False. Note that the AST *might* still be False (i.e.,
        if it were simplified via Z3), but it's hard to quickly tell that.
        '''
        return self._claripy.is_false(self)

    def _simplify_And(self):
        if self.args[0].is_false() or self.args[1].is_false():
            return BoolI(self._claripy, False)
        elif self.args[0].is_true():
            return self.args[1].simplified
        elif self.args[1].is_true():
            return self.args[0].simplified
        else:
            return self

    def _simplify_Or(self):
        if self.args[0].is_true() or self.args[1].is_true():
            return BoolI(self._claripy, True)
        elif self.args[0].is_false():
            return self.args[1].simplified
        elif self.args[1].is_false():
            return self.args[0].simplified
        else:
            return self


Bool.__eq__ = op('__eq__', (Bool, Bool), Bool)
Bool.__ne__ = op('__ne__', (Bool, Bool), Bool)

def BoolI(claripy, model, **kwargs):
    return Bool(claripy, 'I', (model,), **kwargs)
