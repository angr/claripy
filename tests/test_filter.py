import claripy

class AnnotationA(object):
    def __init__(self, v):
        self.v = v

def test_custom_filter():
    def custom_filter(e):
        return e.annotate_outer(AnnotationA(1337))

    b = claripy.BVV(1, 32)
    a = claripy.BVS('a', 32, filters=(custom_filter,) + b.filters)
    assert next(iter((a+b).outer_annotations)).v == 1337

def test_nosimplify():
    a = claripy.BVS('a', 32, filters=())
    assert a.depth == 1
    b = a + 0
    assert b.depth == 2

if __name__ == '__main__':
    test_custom_filter()
    test_nosimplify()
