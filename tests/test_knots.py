import claripy

def test_fast_atoi():
    s = claripy.SolverKnots()
    input_string = claripy.BVS('input', 30*8)
    atoi_of_that = claripy.Atoi(input_string, 32)
    s.add(atoi_of_that * 20 > 300)
    s.add(atoi_of_that * 20 < 400)
    s.add(atoi_of_that < 10000)
    #s.add(input_string.chop(8)[2] == b'1')
    intvals = set()
    for val in s.eval(input_string, 5):
        strval = val.to_bytes(len(input_string) // 8, 'big')
        try:
            chop_strval = strval[:min(i for i, c in enumerate(strval) if not chr(c).isdigit())]
        except ValueError:
            chop_strval = strval
        intval = int(chop_strval)
        assert intval * 20 > 300
        assert intval * 20 < 400
        assert intval < 10000
        intvals.add(intval)
    assert len(intvals) == 4

if __name__ == '__main__':
    test_fast_atoi()
