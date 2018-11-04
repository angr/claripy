import claripy

def test_fast_atoi():
    s = claripy.SolverKnots()
    input_string = claripy.BVS('input', 30*8)
    atoi_of_that = claripy.Atoi(input_string, 32)
    s.add(atoi_of_that * 20 > 300)
    s.add(atoi_of_that * 20 < 400)
    s.add(atoi_of_that < 10000)
    #s.add(input_string.chop(8)[2] == b'1')

    assert 15 < s.eval(atoi_of_that, 1)[0] < 20
    assert not s.satisfiable(extra_constraints=(atoi_of_that > 20,))

    intvals = set()
    for val in s.eval(input_string, 5):
        # parse the int out of the result string and make sure we get only a specific set of results!
        strval = val.to_bytes(len(input_string) // 8, 'big')
        if not strval.isdigit():
            strval = strval[:min(i for i, c in enumerate(strval) if not chr(c).isdigit())]

        intvals.add(int(strval))
    assert intvals == {16, 17, 18, 19}

if __name__ == '__main__':
    test_fast_atoi()
