from __future__ import annotations

import claripy
from claripy.algorithm.bool_check import is_true


# For large tables, ite_dict that uses a binary search tree instead of a "linear" search tree.
# This improves Z3 search capability (eliminating branches) and decreases recursion depth:
# linear search trees make Z3 error out on tables larger than a couple hundred elements.)
def ite_dict(i, d, default):
    """
    Return an expression of if-then-else trees which expresses a switch tree
    :param i: The variable which may take on multiple values affecting the final result
    :param d: A dict mapping possible values for i to values which the result could be
    :param default: A default value that the expression should take on if `i` matches none of the keys of `d`
    :return: An expression encoding the result of the above
    """
    # for small dicts fall back to the linear implementation
    if len(d) < 4:
        return ite_cases([(i == c, v) for c, v in d.items()], default)

    # otherwise, binary search.
    # Find the median:
    keys = list(d.keys())
    keys.sort()
    split_val = keys[(len(keys) - 1) // 2]

    # split the dictionary
    dictLow = {c: v for c, v in d.items() if c <= split_val}
    dictHigh = {c: v for c, v in d.items() if c > split_val}

    valLow = ite_dict(i, dictLow, default)
    valHigh = ite_dict(i, dictHigh, default)
    return claripy.If(i <= split_val, valLow, valHigh)


def ite_cases(cases, default):
    """
    Return an expression of if-then-else trees which expresses a series of alternatives

    :param cases: A list of tuples (c, v). `c` is the condition under which `v` should be the result of the expression
    :param default: A default value that the expression should take on if none of the `c` conditions are satisfied
    :return: An expression encoding the result of the above
    """
    sofar = default
    for c, v in reversed(list(cases)):
        if is_true(v == sofar):
            continue
        sofar = claripy.If(c, v, sofar)
    return sofar


def reverse_ite_cases(ast):
    """
    Given an expression created by `ite_cases`, produce the cases that generated it
    :param ast:
    :return:
    """
    queue = [(claripy.true(), ast)]
    while queue:
        condition, ast = queue.pop(0)
        if ast.op == "If":
            queue.append((claripy.And(condition, ast.args[0]), ast.args[1]))
            queue.append((claripy.And(condition, claripy.Not(ast.args[0])), ast.args[2]))
        else:
            yield condition, ast


def constraint_to_si(expr):
    """
    Convert a constraint to SI if possible.

    :param expr:
    :return:
    """

    satisfiable = True
    replace_list = []

    satisfiable, replace_list = claripy.backends.vsa.constraint_to_si(expr)

    # Make sure the replace_list are all ast.bvs
    for i in range(len(replace_list)):  # pylint:disable=consider-using-enumerate
        ori, new = replace_list[i]
        if not isinstance(new, claripy.ast.Base):
            new = claripy.BVS(
                new.name, new._bits, min=new._lower_bound, max=new._upper_bound, stride=new._stride, explicit_name=True
            )
            replace_list[i] = (ori, new)

    return satisfiable, replace_list
