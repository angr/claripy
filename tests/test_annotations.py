import claripy

class AnnotationA(object):
    def __init__(self, letter, number):
        self.letter = letter
        self.number = number

class AnnotationD(object):
    pass

class BackendA(claripy.Backend):
    def __init__(self):
        claripy.Backend.__init__(self)

    def _convert(self, r):
        return 0

    def _default_op(self, op, *args):
        return sum(args)

    def apply_annotation(self, o, a):
        return o + a.number

ba = BackendA()

def test_backend():
    x = claripy.BVV(10, 32).annotate_outer(AnnotationA('a', 1))
    assert ba.convert(x) == 1

def test_simplification():
    x = claripy.BVS('x', 32).annotate_inline(AnnotationA('a', 1))
    y = x ^ x
    assert y.structure.depth == 1
    assert len(y.structure.annotations) == 0
    assert ba.convert(y) == 0

    x = claripy.BVS('x', 32).annotate_outer(AnnotationA('a', 1))
    y = x ^ x
    assert len(y.outer_annotations) == 1
    assert ba.convert(y) == 1

def test_annotations():
    x = claripy.BVS('x', 32) + 1
    a1 = AnnotationA('a', 1)
    a2 = AnnotationA('a', 1)

    x1 = x.annotate_outer(a1)
    x2 = x1.annotate_outer(a2)
    x2a = x.annotate_outer(a1,a2)
    x2 = x1.annotate_outer(a2)
    x2a = x.annotate_outer(a1,a2)
    x3 = x.annotate_inline(a1)
    x4 = x3.annotate_inline(a2)
    x4a = x.annotate_inline(a1, a2)

    assert x.variables == x1.variables
    assert x.variables == x2.variables
    assert x.variables == x2a.variables
    assert x.variables == x3.variables
    assert x.variables == x4.variables
    assert x.variables == x4a.variables

    assert x is not x1
    assert x is not x2
    assert x is not x3
    assert x1 is not x2
    assert x2 is x2a
    assert x4 is x4a

    assert x.op == x1.op
    assert x.outer_annotations == frozenset()
    assert x1.outer_annotations == frozenset((a1,))
    assert x2.outer_annotations == frozenset((a1,a2))
    assert x4.structure.annotations == (a1,a2)

    assert ba.convert(x) == 0
    assert ba.convert(x1) == 1
    assert ba.convert(x2) == 2
    assert ba.convert(x3) == 1
    assert ba.convert(x4) == 2
    assert ba.convert(x1*1) == 1
    assert ba.convert(x1*x3) == 2

    assert claripy.backends.z3.convert(x).eq(claripy.backends.z3.convert(x3))

def test_eagerness():
    x = claripy.BVV(10, 32).annotate_outer(AnnotationD())
    y = x + 1
    assert y.outer_annotations == x.outer_annotations

if __name__ == '__main__':
    test_annotations()
    test_backend()
    test_eagerness()
    test_simplification()
