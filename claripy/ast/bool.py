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
        if any(a.is_false() for a in self.args):
            return BoolI(self._claripy, False)
        else:
            new_args = [ a.simplified for a in self.args if not a.is_true() ]
            if len(new_args) == 0:
                return BoolI(self._claripy, True)
            else:
                return Bool(self._claripy, self.op, new_args)

    def _simplify_Or(self):
        if any(a.is_true() for a in self.args):
            return BoolI(self._claripy, True)
        else:
            new_args = [ a.simplified for a in self.args if not a.is_false() ]
            if len(new_args) == 0:
                return BoolI(self._claripy, False)
            else:
                return Bool(self._claripy, self.op, new_args)


Bool.__eq__ = op('__eq__', (Bool, Bool), Bool)
Bool.__ne__ = op('__ne__', (Bool, Bool), Bool)

def BoolI(claripy, model, **kwargs):
    return Bool(claripy, 'I', (model,), **kwargs)
