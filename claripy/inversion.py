from .ast.bv import BVS, BVV, Concat, Itoa

class Inversion(object):
    def __init__(self, value, formulae):
        self.value = value
        self.formulae = formulae

    @property
    def live(self):
        return self.value.op == 'BVS'

    @property
    def very_live(self):
        is_temp(self.value)

    def apply(self, temp, value, replacement):
        formulae = {k: v.replace(value, replacement) for k, v in self.formulae.iteritems()}
        if not is_temp(value):
            formulae[value.cache_key] = replacement
        return Inversion(temp, formulae)

def make_temp(size):
    return BVS('invertemp', size)

def is_temp(v):
    return v.op == 'BVS' and v.args[0].startswith('invertemp')

def invert(ast):
    if type(ast) in (int, long, bytes, unicode):
        return Inversion(ast, {})
    if ast.op in ('BVV', 'BVS'):
        return Inversion(ast, {})

    sz = len(ast)
    iargs = map(invert, ast.args)
    result_formulae, wash = formulae_union(iargs)

    if wash:
        pass

    elif ast.op == 'Concat':
        if all(c.live for c in iargs):
            t = make_temp(sz)
            r = Inversion(t, result_formulae)
            sofar = 0
            for c in iargs:
                if c.value.cache_key in r.formulae:
                    wash = True
                    break
                r = r.apply(t, c.value, t[sz - sofar + 1: sz - sofar + len(c.value)])
            else:
                return r

    elif ast.op == 'Extract':
        c = iargs[2]
        if c.live:
            t = make_temp(sz)
            return c.apply(t, c.value, Concat(BVV(0, len(c.value) - ast.args[0] - 1), t, BVV(0, ast.args[1])))

    elif ast.op == 'Atoi':
        c = iargs[0]
        if c.live:
            t = make_temp(sz)
            return c.apply(t, c.value, Itoa(t, len(ast.args[0]) // 8))

    #elif ast.op == '__add__':
    #    if len([c for c in iargs l # ?????????????????????????

    if wash:
        return Inversion(ast, result_formulae)
    else:
        return Inversion(type(ast)(ast.op, [inv.value for inv in iargs]), result_formulae)

def formulae_union(iargs):
    result_formulae = {}
    wash = False

    for iarg in iargs:
        for k in iarg.formulae:
            if wash:
                result_formulae[k] = None
            else:
                if k in result_formulae:
                    wash = True
                    for k2 in result_formulae:
                        result_formulae[k2] = None
                    result_formulae[k] = None
                else:
                    result_formulae[k] = iarg.formulae[k]
    return result_formulae, wash
