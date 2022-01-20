#!/usr/bin/env python3

def prep():
    import os
    from os import path
    import sys
    import glob
    # Paths
    build = path.expanduser('~/native/.build.debug/ffi/')
    pya = path.expanduser('~/native/python_api/')
    assert path.isdir(pya) and path.isdir(build), 'Fix me'
    basen = 'claricpp_ffi.o'
    # Rm old
    lib1 = path.join(pya, basen)
    if path.exists(lib1):
        os.remove(lib1)
    lib2 = glob.glob(path.join(pya, 'claricpp_ffi.*.so'))
    assert len(lib2) <= 1, 'Fix me'
    if len(lib2) == 1:
        os.remove(lib2[0])
    # Use new
    os.link(path.join(build, basen), path.join(pya, basen))
    libn = glob.glob(path.join(build, 'claricpp_ffi.*.so'))
    assert len(libn) == 1, 'Fix me: ' + str(libn)
    os.link(libn[0], path.join(pya, path.basename(libn[0])))
prep()

from python_api import *
from python_api.create import bool_v, bv_v, if_, add
from python_api.z3 import Z3

def test():
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
test()