from ..operations import expression_arithmetic_operations, expression_comparator_operations, expression_bitwise_operations

from .base import make_methods
from .bits import Bits

class BV(Bits):

    # TODO: do these go on Bits or BV?
    def chop(self, bits=1):
        '''
        Chops an AST into ASTs of size 'bits'. Obviously, the length of the AST must be
        a multiple of bits.
        '''
        s = len(self)
        if s % bits != 0:
            raise ValueError("expression length (%d) should be a multiple of 'bits' (%d)" % (len(self), bits))
        elif s == bits:
            return [ self ]
        else:
            return list(reversed([ self[(n+1)*bits - 1:n*bits] for n in range(0, s / bits) ]))

    @property
    def reversed(self):
        '''
        The reversed AST.
        '''
        return self._do_op('Reverse', collapsible=False)

    def __getitem__(self, rng):
        '''
        Extracts bits from the AST. ASTs are indexed weirdly. For a 32-bit AST:

            a[31] is the *LEFT* most bit, so it'd be the 0 in

                01111111111111111111111111111111

            a[0] is the *RIGHT* most bit, so it'd be the 0 in

                11111111111111111111111111111110

            a[31:30] are the two leftmost bits, so they'd be the 0s in:

                00111111111111111111111111111111

            a[1:0] are the two rightmost bits, so they'd be the 0s in:

                11111111111111111111111111111100

        @returns the new AST.
        '''
        if type(rng) is slice:
            return self._claripy.Extract(int(rng.start), int(rng.stop), self)
        else:
            return self._claripy.Extract(int(rng), int(rng), self)

    def zero_extend(self, n):
        '''
        Zero-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.zero_extend(4)
            b is BVV(0b00001111)
        '''
        return self._claripy.ZeroExt(n, self)

    def sign_extend(self, n):
        '''
        Sign-extends the AST by n bits. So:

            a = BVV(0b1111, 4)
            b = a.sign_extend(4)
            b is BVV(0b11111111)
        '''
        return self._claripy.SignExt(n, self)

    def concat(self, *args):
        '''
        Concatenates this AST with the ASTs provided.
        '''
        return self._claripy.Concat(self, *args)

make_methods(BV, expression_arithmetic_operations | expression_comparator_operations | expression_bitwise_operations)
