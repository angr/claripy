import claripy

class AnnotationA(claripy.Annotation):
    def __init__(self, v):
        self.v = v

def test_custom_filter():
    def custom_filter(e):
        return e.annotate(AnnotationA(1337))

    b = claripy.BVV(1, 32)
    a = claripy.BVS('a', 32, filters=(custom_filter,) + b.filters)
    assert (a+b).annotations[0].v == 1337

def test_nosimplify():
    a = claripy.BVS('a', 32, filters=())
    assert a.depth == 1
    b = a + 0
    assert b.depth == 2

if __name__ == '__main__':
    test_custom_filter()
    test_nosimplify()
