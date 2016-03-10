import sys
import time
import os
import logging

import nose

import angr
import simuvex
from  claripy.vsa import StridedInterval

l = logging.getLogger("angr_tests")

def test_division():
    # non-overlapping
    
    # simple case 1
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # <4>0x1[0x0, 0x1]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x0, 0x1]"
    assert str(op1.udiv(op2)) == "<4>0x1[0x0, 0x1]"
    
    # simple case 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=1)
    # <4>0x1[0xa, 0xc]
    assert str(op1.sdiv(op2)) == "<4>0x1[0xa, 0xc]"
    assert str(op1.udiv(op2)) == "<4>0x1[0xa, 0xc]"
    
    # simple case 3
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-2)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=-2)
    #udiv:  <4>0x1[0x0, 0x1]
    #sdiv:  <4>0x1[0xc, 0x4]
    assert str(op1.udiv(op2)) == "<4>0x1[0x0, 0x1]"
    assert str(op1.sdiv(op2)) == "<4>0x1[0xc, 0x4]"
    
    # simple case 4 : Result should be zero
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
    # BOT
    assert str(op1.sdiv(op2)) == "<4>[EmptySI]"
    assert str(op1.udiv(op2)) == "<4>[EmptySI]"
    
    
    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=4, upper_bound=6)
    #udiv: <4>0x0[0x0, 0x0]
    #sdiv: <4>0x0[0x0, 0x0]
    assert str(op1.udiv(op2)) == "<4>0x0[0x0, 0x0]"
    assert str(op1.sdiv(op2)) == "<4>0x0[0x0, 0x0]"
    
    
    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-3, upper_bound=-1)
    #sdiv: <4>0x1[0x1, 0x6]
    #udiv: <4>0x0[0x0, 0x0]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x1, 0x6]"
    assert str(op1.udiv(op2)) == "<4>0x0[0x0, 0x0]"
    
    # one in 0-hemisphere and one in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
    #sdiv: <4>0x1[0xc, 0xf]
    #udiv: <4>0x0[0x0, 0x0]
    assert str(op1.sdiv(op2)) == "<4>0x1[0xc, 0xf]"
    assert str(op1.udiv(op2)) == "<4>0x0[0x0, 0x0]"
    
    # Overlapping 
    
    # case a of figure 2
    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=6)
    #sdiv: <4>0x1[0x0, 0x3]
    #udiv: <4>0x1[0x0, 0x3]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x0, 0x3]"
    assert str(op1.udiv(op2)) == "<4>0x1[0x0, 0x3]"
    
    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-7, upper_bound=-1)
    #sdiv: <4>0x1[0x0, 0x6]
    #udiv: <4>0x1[0x0, 0x1]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x0, 0x6]"
    assert str(op1.udiv(op2)) == "<4>0x1[0x0, 0x1]"
    
    # case b Fig 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=7, upper_bound=5)
    #sdiv: <4>0x1[0x0, 0xf]
    #udiv: <4>0x1[0x0, 0xa]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x0, 0xf]"
    assert str(op1.udiv(op2)) == "<4>0x1[0x0, 0xa]"
    
    # case c Fig 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=5)
    #sdiv: <4>0x1[0x0, 0xe]
    #udiv: <4>0x1[0x0, 0xa]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x0, 0xe]"
    assert str(op1.udiv(op2)) == "<4>0x1[0x0, 0xa]"
    
    # Strided Tests
    
    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=4, upper_bound=6)
    # sdiv: <4>0x0[0x0, 0x0]
    # udiv: <4>0x0[0x0, 0x0]
    assert str(op1.sdiv(op2)) == "<4>0x0[0x0, 0x0]"
    assert str(op1.udiv(op2)) == "<4>0x0[0x0, 0x0]"
    
    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=-3, upper_bound=-1)
    # sdiv: <4>0x1[0x1, 0x6]
    # udiv: <4>0x0[0x0, 0x0]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x1, 0x6]"
    assert str(op1.udiv(op2)) == "<4>0x0[0x0, 0x0]"
    
    # Overlapping case 1
    op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
    op2 = StridedInterval(bits=4, stride=3, lower_bound=7, upper_bound=3)
    # sdiv: <4>0x1[0x9, 0x7]
    # udiv: <4>0x1[0x0, 0x9]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x9, 0x7]"
    assert str(op1.udiv(op2)) == "<4>0x1[0x0, 0x9]"
    
    # Overlapping case 2
    op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=1, upper_bound=3)
    # sdiv: <4>0x1[0x1, 0xd]
    # udiv: <4>0x1[0x1, 0x9]
    assert str(op1.sdiv(op2)) == "<4>0x1[0x1, 0xd]"
    assert str(op1.udiv(op2)) == "<4>0x1[0x1, 0x9]"
    

def test_multiplication():
    # non-overlapping
    
    # simple case 1
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # <4>0x2[0x2, 0x6]
    assert str(op1.mul(op2)) == "<4>0x2[0x2, 0x6]"
    
    # simple case 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=1)
    # <4>0x1[0xa, 0xc]
    assert str(op1.mul(op2)) == "<4>0x1[0xa, 0xc]"
    
    # simple case 3
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-2)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=-2)
    # Stride should be 2.
    # NOTE: previous result was: <4>0x1[0x4, 0x0] which is wrong.
    # possible values of 1[3,e] * 0[e,e] on 4 bits are [a, 8, 6, 4, 2, 0, e, c]
    # in the previous SI 2 was not present.
    assert str(op1.mul(op2)) == "<4>0x2[0x2, 0x0]"
    
    # simple case 4 : Result should be zero
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
    # <4>0x0[0x0, 0x0]
    assert str(op1.mul(op2)) == "<4>0x0[0x0, 0x0]"
    
    
    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=4, upper_bound=6)
    # Result: <4>0x1[0x4, 0x2]
    assert str(op1.mul(op2)) == "<4>0x1[0x4, 0x2]"
    
    
    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-3, upper_bound=-1)
    # Result <4>0x1[0x4, 0x2]
    assert str(op1.mul(op2)) == "<4>0x1[0x4, 0x2]"
    
    # one in 0-hemisphere and one in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
    # TOP
    assert str(op1.mul(op2)) == "<4>0x1[0x0, 0xf]"
    
    # Overlapping 
    
    # case a of figure 2
    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=6)
    # TOP
    assert str(op1.mul(op2)) == "<4>0x1[0x0, 0xf]"
    
    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-7, upper_bound=-1)
    # TOP
    assert str(op1.mul(op2)) == "<4>0x1[0x0, 0xf]"
    
    # case b Fig 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=7, upper_bound=5)
    # <4>0x1[0x0, 0xf]
    assert str(op1.mul(op2)) == "<4>0x1[0x0, 0xf]"
    
    # case c Fig 2
    op1 = StridedInterval(bits=4, stride=1, lower_bound=3, upper_bound=-6)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=5)
    # <4>0x1[0x0, 0xf]
    assert str(op1.mul(op2)) == "<4>0x1[0x0, 0xf]"
    
    # Strided Tests
    
    # Both in 0-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=3)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=4, upper_bound=6)
    # <4>0x1[0x4, 0x2]
    assert str(op1.mul(op2)) == "<4>0x1[0x4, 0x2]"
    
    # Both in 1-hemisphere
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-6, upper_bound=-4)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=-3, upper_bound=-1)
    # <4>0x1[0x4, 0x2]
    assert str(op1.mul(op2)) == "<4>0x1[0x4, 0x2]"
    
    # Overlapping case 1
    op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
    op2 = StridedInterval(bits=4, stride=3, lower_bound=7, upper_bound=3)
    # <4>0x1[0x0, 0xf]
    assert str(op1.mul(op2)) == "<4>0x1[0x0, 0xf]"
    
    # Overlapping case 2
    op1 = StridedInterval(bits=4, stride=2, lower_bound=3, upper_bound=-7)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=1, upper_bound=3)
    # TOP
    assert str(op1.mul(op2)) == "<4>0x1[0x0, 0xf]"
    
    

def test_subtraction():
    # Basic Interval Tests
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
    # Result should be TOP
    assert str(op1.sub(op2)) == "<4>0x1[0x0, 0xf]"
    
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=6)
    # Result should be 1,[15, 1]
    # print str(op1.sub(op2))
    assert str(op1.sub(op2)) == "<4>0x1[0xb, 0x5]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # Result should be 1,[15, 5]
    assert str(op1.sub(op2)) == "<4>0x1[0xf, 0x5]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # Result should be 1,[-4, 5]
    assert str(op1.sub(op2)) == "<4>0x1[0xc, 0x5]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
    # Result should be 1,[1, 7]
    assert str(op1.sub(op2)) == "<4>0x1[0x1, 0x7]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
    # Result should be 1,[6, 8]
    # print str(op1.sub(op2))
    assert str(op1.sub(op2)) == "<4>0x1[0x2, 0xc]"
    
    # Strided Tests
    op1 = StridedInterval(bits=4, stride=2, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
    # Result should be TOP
    assert str(op1.sub(op2)) == "<4>0x1[0x0, 0xf]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=2, upper_bound=6)
    # Result should be 1,[15, 1]
    assert str(op1.sub(op2)) == "<4>0x1[0xb, 0x5]"
    

def test_add():
    # Basic Interval Tests
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
    # Result should be TOP
    assert str(op1.add(op2)) == "<4>0x1[0x0, 0xf]"
    
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=6)
    # Result should be 1,[3, 13]
    assert str(op1.add(op2)) == "<4>0x1[0x3, 0xd]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # Result should be 1,[3, 9]
    assert str(op1.add(op2)) == "<4>0x1[0x3, 0x9]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=2, upper_bound=2)
    # Result should be 1,[0,9]
    assert str(op1.add(op2)) == "<4>0x1[0x0, 0x9]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=0)
    # Result should be 1,[1,7]
    assert str(op1.add(op2)) == "<4>0x1[0x1, 0x7]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=-5, upper_bound=-1)
    # Result should be 1,[-4, 6]
    assert str(op1.add(op2)) == "<4>0x1[0xc, 0x6]"
    
    # Strided Tests
    op1 = StridedInterval(bits=4, stride=2, lower_bound=-2, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=1, lower_bound=0, upper_bound=-6)
    # Result should be TOP
    assert str(op1.add(op2)) == "<4>0x1[0x0, 0xf]"
    
    op1 = StridedInterval(bits=4, stride=1, lower_bound=1, upper_bound=7)
    op2 = StridedInterval(bits=4, stride=2, lower_bound=2, upper_bound=6)
    # Result should be 1,[3, 13]
    assert str(op1.add(op2)) == "<4>0x1[0x3, 0xd]"
    

if __name__ == "__main__":
    # Addition tests
    l.info("Performing Add Tests")
    test_add()
    l.info("Performing Subtraction Tests")
    test_subtraction()
    l.info("Performing Multiplication Tests")
    test_multiplication()
    l.info("Performing Division Tests")
    test_division()
    print "[+] All Tests Passed"
