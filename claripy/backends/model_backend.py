from ..backend import Backend

class ModelBackend(Backend):
    '''
    A ModelBackend is a backend that does not support solving (and, thus,
    constraints), but still supports max(), min(), eval(), etc.
    '''

    def __init__(self):
        Backend.__init__(self)

    #
    # These functions provide solving and evaluation support.
    #

    def eval(self, expr, n, result=None):
        '''
        This function returns up to n possible solutions for expression expr.

        @param expr: expression (claripy.E object) to evaluate
        @param n: number of results to return
        @param result: a cached Result from the last constraint solve
        @returns a sequence of up to n results (backend objects)
        '''
        return self._eval(self.convert(expr), n, result=result)

    def _eval(self, expr, n, result=None): #pylint:disable=unused-argument,no-self-use
        '''
        This function returns up to n possible solutions for expression expr.

        @param expr: expression (backend object) to evaluate
        @param n: number of results to return
        @param result: a cached Result from the last constraint solve
        @returns a sequence of up to n results (backend objects)
        '''
        raise BackendError("backend doesn't support eval()")

    def min(self, expr, result=None):
        '''
        Return the minimum value of expr.

        @param expr: expression (claripy.E object) to evaluate
        @param result: a cached Result from the last constraint solve
        @returns the minimum possible value of expr (backend object)
        '''
        return self._min(self.convert(expr), result=result)

    def _min(self, expr, result=None): #pylint:disable=unused-argument,no-self-use
        '''
        Return the minimum value of expr.

        @param expr: expression (backend object) to evaluate
        @param result: a cached Result from the last constraint solve
        @returns the minimum possible value of expr (backend object)
        '''
        raise BackendError("backend doesn't support min()")

    def max(self, expr, result=None):
        '''
        Return the maximum value of expr.

        @param expr: expression (claripy.E object) to evaluate
        @param result: a cached Result from the last constraint solve
        @returns the maximum possible value of expr (backend object)
        '''
        return self._max(self.convert(expr), result=result)

    def _max(self, expr, result=None): #pylint:disable=unused-argument,no-self-use
        '''
        Return the maximum value of expr.

        @param expr: expression (backend object) to evaluate
        @param result: a cached Result from the last constraint solve
        @returns the maximum possible value of expr (backend object)
        '''
        raise BackendError("backend doesn't support max()")

    def solution(self, expr, v, result=None):
        '''
        Return True if v is a solution of expr with the extra constraints, False otherwise.

        @param expr: expression (claripy.E) to evaluate
        @param v: the proposed solution (claripy.E)
        @param result: a cached Result from the last constraint solve
        @returns True if v is a solution of expr, False otherwise
        '''

        return self._solution(self.convert(expr), self.convert(v), result=result)

    def _solution(self, expr, v, result=None): #pylint:disable=unused-argument,no-self-use
        '''
        Return True if v is a solution of expr with the extra constraints, False otherwise.

        @param expr: expression (backend object) to evaluate
        @param v: the proposed solution (backend object)
        @param result: a cached Result from the last constraint solve
        @returns True if v is a solution of expr, False otherwise
        '''

        raise BackendError("backend doesn't support solution()")

    @staticmethod
    def has_false(o):
        return o == False

    @staticmethod
    def has_true(o):
        return o == True

    @staticmethod
    def is_false(o):
        return o == False

    @staticmethod
    def is_true(o):
        return o == True

    def size(self, a, result=None):
        '''
        This should return the size of an expression.

        @param a: the claripy A object
        '''
        return self._size(self.convert(a, result=result))

    def _size(self, o, result=None): #pylint:disable=no-self-use,unused-argument
        '''
        This should return the size of an object.

        @param o: the (backend-native) object
        '''
        raise BackendError("backend doesn't support solution()")

    def name(self, a, result=None):
        '''
        This should return the name of an expression.

        @param a: the claripy A object
        '''
        return self._name(self.convert(a, result=result))

    def _name(self, o, result=None): #pylint:disable=no-self-use,unused-argument
        '''
        This should return the name of an object.

        @param o: the (backend-native) object
        '''
        raise BackendError("backend doesn't support solution()")

    def identical(self, a, b, result=None):
        '''
        This should return whether a is identical to b. Of course, this isn't always
        clear. A True should mean that it is definitely identical. False
        means that, conservitivly, it might not be.

        @param a: a claripy A object
        @param b: a claripy A object
        '''
        return self._identical(self.convert(a, result=result), self.convert(b, result=result))

    def _identical(self, a, b, result=None): #pylint:disable=no-self-use,unused-argument
        '''
        This should return whether a is identical to b. Of course, this isn't always
        clear. A True should mean that it is definitely identical. False
        means that, conservitivly, it might not be.

        @param a: the (backend-native) object
        @param b: the (backend-native) object
        '''
        raise BackendError("backend doesn't support solution()")

from ..errors import BackendError
