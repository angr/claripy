import operator
import itertools
bitvec_counter = itertools.count()

import logging
l = logging.getLogger('claripy.claripy')

class Claripy(object):
    def __init__(self, model_backends, solver_backends, datalayer, parallel=None):
        self.solver_backends = solver_backends
        self.model_backends = model_backends
        self.datalayer = datalayer
        self.unique_names = True
        self.parallel = parallel if parallel else False

        self.true = self.BoolVal(True)
        self.false = self.BoolVal(False)

    #
    # Backend management
    #
    def backend_of_type(self, b_type):
        for b in self.model_backends + self.solver_backends:
            if type(b) is b_type:
                return b
        return None

    #
    # Solvers
    #
    def solver(self):
        '''
        Returns a new solver.
        '''
        raise NotImplementedError()

    #
    # Operations
    #

    def wrap(self, o):
        if type(o) == BVV:
            return self.datalayer.make_expression(o)
        else:
            return o

    def _do_op(self, name, args, variables=None, symbolic=None, raw=False, simplified=False):
        for b in self.model_backends:
            try:
                if raw: r = b.call(name, args)
                else:   r = b.call_expr(name, args)
                break
            except BackendError:
                continue
        else:
            # Special case for Reverse
            r = None
            if name == 'Reverse':
                arg = args[0]
                if isinstance(arg, E) and \
                        isinstance(arg._actual_model, A) and \
                        arg._model.op == 'Reverse':
                    # Unpack it :-)
                    r = arg._model.args[0]

            if r is None:
                r = A(name, args)

        if symbolic is None:
            symbolic = any(arg.symbolic if isinstance(arg, E) else False for arg in args)
        if variables is None:
            all_variables = ((arg.variables if isinstance(arg, E) else set()) for arg in args)
            variables = reduce(operator.or_, all_variables, set())

        return self.datalayer.make_expression(r, variables=variables, symbolic=symbolic, simplified=simplified)

    def BitVec(self, name, size, explicit_name=None):
        explicit_name = explicit_name if explicit_name is not None else False
        if self.unique_names and not explicit_name:
            name = "%s_%d_%d" % (name, bitvec_counter.next(), size)
        return self._do_op('BitVec', (name, size), variables={ name }, symbolic=True, raw=True, simplified=True)

    def BitVecVal(self, *args):
        return self.datalayer.make_expression(BVV(*args), variables=set(), symbolic=False, simplified=True)
        #return self._do_op('BitVecVal', args, variables=set(), symbolic=False, raw=True)

    # Bitwise ops
    def LShR(self, *args): return self._do_op('LShR', args)
    def SignExt(self, *args): return self._do_op('SignExt', args)
    def ZeroExt(self, *args): return self._do_op('ZeroExt', args)
    def Extract(self, *args): return self._do_op('Extract', args)
    def Concat(self, *args): return self._do_op('Concat', args)
    def RotateLeft(self, *args): return self._do_op('RotateLeft', args)
    def RotateRight(self, *args): return self._do_op('RotateRight', args)
    def Reverse(self, o, lazy=True):
        if type(o) is not E or not lazy:
            return self._do_op('Reverse', (o,))

        if len(o._pending_operations) == 0 or o._pending_operations[-1] != "Reverse":
            if isinstance(o._model, A) and o._model.op == 'Reverse':
                # There is a Reverse operation inside. We wanna undo that
                a = o._model
                e = a.args[0]
            else:
                e = o.copy()
                e.objects.clear()
                e._pending_operations.append("Reverse")
            return e
        elif o._pending_operations[-1] == "Reverse":
            e = o.copy()
            e.objects.clear()
            e._pending_operations.pop()
            return e

    #
    # Strided interval
    #
    def StridedInterval(self, **kwargs):
        si = StridedInterval(**kwargs)
        return E(self, model=si, variables=set(), symbolic=False)

    #
    # Boolean ops
    #
    def BoolVal(self, *args):
        return self.datalayer.make_expression(args[0], variables=set(), symbolic=False, simplified=True)
        #return self._do_op('BoolVal', args, variables=set(), symbolic=False, raw=True)

    def And(self, *args): return self._do_op('And', args)
    def Not(self, *args): return self._do_op('Not', args)
    def Or(self, *args): return self._do_op('Or', args)
    def ULT(self, *args): return self._do_op('ULT', args)
    def ULE(self, *args): return self._do_op('ULE', args)
    def UGE(self, *args): return self._do_op('UGE', args)
    def UGT(self, *args): return self._do_op('UGT', args)

    #
    # Other ops
    #
    def If(self, *args):
        if len(args) != 3: raise ClaripyOperationError("invalid number of args passed to If")
        return self._do_op('If', args)

    #def size(self, *args): return self._do_op('size', args)

    def ite_dict(self, i, d, default):
        return self.ite_cases([ (i == c, v) for c,v in d.items() ], default)

    def ite_cases(self, cases, default):
        sofar = default
        for c,v in reversed(cases):
            sofar = self.If(c, v, sofar)
        return sofar

    def simplify(self, e):
        for b in self.model_backends:
            try: return b.simplify_expr(e)
            except BackendError: pass

        l.debug("Simplifying via solver backend")

        for b in self.solver_backends:
            try: return b.simplify_expr(e)
            except BackendError: pass

        l.warning("Unable to simplify expression")
        return e

    def model_object(self, e, result=None):
        for b in self.model_backends:
            try: return b.convert_expr(e, result=result)
            except BackendError: pass
        raise BackendError('no model backend can convert expression')

from .expression import E, A
from .backends.backend import BackendError
from .bv import BVV
from .vsa import StridedInterval
from .errors import ClaripyOperationError
