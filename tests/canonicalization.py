import string
import claripy
import time

for i in string.lowercase[:8] + string.lowercase[-8:]:
    globals()[i] = claripy.BVS(i, 32)

full_test = True

if full_test:
    def can(ast):
        return (ast.canonical_hash(), ast.canonicalize())
else:
    def can(ast):
        return (ast.canonical_hash(), None)

def compare(a1, a2):
    return a1[0] == a2[0] and a1[1] is a2[1]

start = time.time()


assert compare(can(x), can(y))

assert compare(can(x + x + x), can(y + y + y))
assert compare(can(x + x + y),  can(a + b + a))
assert compare(can(a | (b & c)), can((a & b) | c))

assert not compare(can(a | ((a - b) + (c - d))), can(e | ((a - b) + (c - d))))

assert not compare(can((a - b) * (a - b)), can((b - a) * (a - b)))

assert compare(can(a + b + (b - a)),  can((x - y) + x + y))
assert compare(can((a + b) + (b - a)), can((x - y) + (x + y)))

assert compare(can(claripy.Concat(x,    y)), can(claripy.Concat(y,    x)))
assert not compare(can(claripy.Concat(x, y, x)), can(claripy.Concat(x, x, y)))

assert compare(can((a + b) + c), can(a + (b + c)))
assert compare(can( a + b  + c), can((a + b) + c))

assert compare(can(a + b + c + d), can(((a + b) + c) + d))

assert not compare(can(a + 2), can(a + 4))
assert compare(can(x + 2), can(x + 2))

assert not compare(can(x + y), can(x * y))

# Do we want to implement this? (probably as a simplifier)
# assert can(x - 1) == can(x + -1)

assert compare(can(claripy.FPS("a", claripy.FSORT_DOUBLE)), can(claripy.FPS("b", claripy.FSORT_DOUBLE)))
assert not compare(can(claripy.FPS("a", claripy.FSORT_DOUBLE)), can(claripy.FPS("b", claripy.FSORT_FLOAT)))
assert not compare(can(claripy.FPS("a", claripy.FSORT_FLOAT)), can(claripy.FPS("b", claripy.FSORT_DOUBLE)))
assert compare(can(claripy.FPS("a", claripy.FSORT_FLOAT)), can(claripy.FPS("b", claripy.FSORT_FLOAT)))

cancer1 = claripy.BVS("j", 32, explicit_name=True)
cancer2 = claripy.BVS("j", 32, explicit_name=True)
assert cancer1 is cancer2
assert compare(can(cancer1), can(cancer2))

assert compare(can((a + 1) == b), can(b == (c + 1)))
assert compare(can((a + 1) <= b), can(b >= (c + 1)))

assert compare(can(a | ((a - b) + (c - d))), can(a | ((c - d) + (a - b))))
assert compare(can(a | ((a - b) + (c - d))), can(b | ((b - c) + (d - e)))) # c and e have the same hash


time_taken = time.time() - start

print "canonicalization tests took", time_taken, "seconds"
