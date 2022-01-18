#!/usr/bin/env python3

from create import *
from z3 import Z3


try:
    tru = bool_v(True)
    bl = 32
    bv1 = bv_v(1, bl)
    bv0 = bv_v(b"0", bl)

    ii = if_(tru, bv1, bv0)

    z3 = Z3()
    simp = z3.simplify(ii)

    print("Start with: if(true) 1 else 0")
    print(repr(ii))
    print("\nSimplify with z3:")
    print(repr(simp))

    print("\nif args: ")
    print(ii.args)
    print("\nSucess")

    bv2 = add(bv1, bv0)
    print(repr(bv2))
# except ClaricppException as e:
#     print('\nCaught')
#     print(e)
#     print('\nDone')

finally:
    print("\nEnd")

# import IPython
# IPython.embed()
# breakpoint()
