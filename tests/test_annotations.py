import claripy

class AnnotationA(claripy.Annotation):
    def __init__(self, letter, number):
        self.letter = letter
        self.number = number
        claripy.Annotation.__init__(self)

class AnnotationB(AnnotationA):
    @property
    def eliminatable(self):
        return False

    @property
    def relocatable(self):
        return False

class AnnotationC(AnnotationA):
    @property
    def eliminatable(self):
        return False

    @property
    def relocatable(self):
        return True

    def relocate(self, src, dst):
        return AnnotationC(self.letter, self.number+1)

class AnnotationD(claripy.Annotation):
    @property
    def eliminatable(self):
        return False

    @property
    def relocatable(self):
        return True

class BackendA(claripy.Backend):
    def __init__(self):
        claripy.Backend.__init__(self)
        self._op_expr['BVV'] = lambda e, result=None: e.args[0]

    def apply_annotation(self, o, a):
        return o + a.number

def test_backend():
    x = claripy.BVV(10, 32).annotate(AnnotationA('a', 1))
    assert BackendA().convert(x) == 11

def test_simplification():
    x = claripy.BVS('x', 32).annotate(AnnotationA('a', 1))
    y = x ^ x
    assert y.depth == 1
    assert len(y.annotations) == 0

    x = claripy.BVS('x', 32).annotate(AnnotationB('a', 1))
    y = x ^ x
    assert y.depth == 2

    x = claripy.BVS('x', 32).annotate(AnnotationC('a', 1))
    y = x ^ x
    assert y.depth == 1
    assert len(y.annotations) == 1
    assert y.annotations[0].number == 2

def test_annotations():
    x = claripy.BVS('x', 32) + 1
    xx = x._apply_to_annotations(lambda a: a)
    assert x is xx

    a1 = AnnotationA('a', 1)
    a2 = AnnotationA('a', 1)

    x1 = x.annotate(a1)
    x2 = x1.annotate(a2)
    x2a = x.annotate(a1,a2)
    x3 = x2.remove_annotation(a1)
    x4 = x3.remove_annotation(a2)
    x5 = x2.remove_annotations({a1,a2})

    assert x.variables == x1.variables
    assert x.variables == x2.variables
    assert x.variables == x2a.variables
    assert x.variables == x3.variables
    assert x.variables == x4.variables
    assert x.variables == x5.variables

    assert x is not x1
    assert x is not x2
    assert x is not x3
    assert x1 is not x2
    assert x1 is not x3
    assert x2 is not x3
    assert x2 is x2a
    assert x is x4
    assert x is x5

    assert x.op == x1.op
    assert x.annotations == ()
    assert x1.annotations == (a1,)
    assert x2.annotations == (a1,a2)
    assert x3.annotations == (a2,)

    assert claripy.backends.z3.convert(x).eq(claripy.backends.z3.convert(x3))

    const = claripy.BVV(1, 32)
    consta = const.annotate(AnnotationB('a', 0))
    const1 = consta + 1
    const1a = const1.annotate(AnnotationB('b', 1))
    const2 = const1a + 1
    # const2 should be (const1a + 1), instead of (1 + 1 + 1)
    # the flatten simplifier for __add__ should not be applied as AnnotationB is not relocatable (and not eliminatable)
    assert const2.depth == 3

def test_eagerness():
    x = claripy.BVV(10, 32).annotate(AnnotationD())
    y = x + 1
    assert y.annotations == x.annotations

if __name__ == '__main__':
    test_annotations()
    test_backend()
    test_eagerness()
