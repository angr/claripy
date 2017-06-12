import string
import claripy
import time

for i in string.lowercase[:8] + string.lowercase[-8:]:
    globals()[i] = claripy.BVS(i, 32)

def can(ast):
    return ast.structure.canonicalize()[1]

start = time.time()


assert can(x) == can(y)

assert  can(x + x + x)  ==  can(y + y + y)
assert  can(x + x + y)  ==  can(a + b + a)
assert can(a | (b & c)) == can((a & b) | c)

assert can(a | ((a - b) + (c - d))) != can(e | ((a - b) + (c - d)))

assert  can(a + b + (b - a))  ==  can((x - y) + x + y)
assert can((a + b) + (b - a)) == can((x - y) + (x + y))

assert can(claripy.Concat(x,    y)) == can(claripy.Concat(y,    x))
assert can(claripy.Concat(x, y, x)) != can(claripy.Concat(x, x, y))

assert can((a + b) + c) == can(a + (b + c))
assert can( a + b  + c) == can((a + b) + c)

assert can(a + b + c + d) == can(((a + b) + c) + d)

assert can(a + 2) != can(a + 4)
assert can(x + 2) == can(x + 2)

# Do we want to implement this? (probably as a simplifier)
# assert can(x - 1) == can(x + -1)

assert can(claripy.FPS("a", claripy.FSORT_DOUBLE)) == can(claripy.FPS("b", claripy.FSORT_DOUBLE))
assert can(claripy.FPS("a", claripy.FSORT_DOUBLE)) != can(claripy.FPS("b", claripy.FSORT_FLOAT))
assert can(claripy.FPS("a", claripy.FSORT_FLOAT))  != can(claripy.FPS("b", claripy.FSORT_DOUBLE))
assert can(claripy.FPS("a", claripy.FSORT_FLOAT))  == can(claripy.FPS("b", claripy.FSORT_FLOAT))

cancer1 = claripy.BVS("j", 32, explicit_name=True)
cancer2 = claripy.BVS("j", 32, explicit_name=True)
assert cancer1 is cancer2
assert can(cancer1) == can(cancer2)

assert can((a + 1) == b) == can(b == (c + 1))
assert can((a + 1) <= b) == can(b >= (c + 1))

assert can(a | ((a - b) + (c - d))) == can(a | ((c - d) + (a - b)))
assert can(a | ((a - b) + (c - d))) == can(b | ((b - c) + (d - e))) # c and e have the same hash


time_taken = time.time() - start

print "took", time_taken, "seconds"
