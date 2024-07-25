# pylint:disable=isinstance-second-argument-not-valid-type
from __future__ import annotations

import collections
import itertools
import operator
from functools import reduce

from . import ast, fp
from .backend_manager import backends


class SimplificationManager:
    def __init__(self):
        self._simplifiers = {
            "Reverse": self.bv_reverse_simplifier,
            "And": self.boolean_and_simplifier,
            "Or": self.boolean_or_simplifier,
            "Not": self.boolean_not_simplifier,
            "Extract": self.extract_simplifier,
            "Concat": self.concat_simplifier,
            "If": self.if_simplifier,
            "__lshift__": self.lshift_simplifier,
            "__rshift__": self.rshift_simplifier,
            "LShR": self.lshr_simplifier,
            "__eq__": self.eq_simplifier,
            "__ne__": self.ne_simplifier,
            "__ge__": self.ge_simplifier,
            "__or__": self.bitwise_or_simplifier,
            "__and__": self.bitwise_and_simplifier,
            "__xor__": self.bitwise_xor_simplifier,
            "__add__": self.bitwise_add_simplifier,
            "__sub__": self.bitwise_sub_simplifier,
            "__mul__": self.bitwise_mul_simplifier,
            "ZeroExt": self.zeroext_simplifier,
            "SignExt": self.signext_simplifier,
            "fpToIEEEBV": self.fptobv_simplifier,
            "fpToFP": self.fptofp_simplifier,
            "StrReverse": self.str_reverse_simplifier,
            "__invert__": self.invert_simplifier,
        }

    def simplify(self, op, args):
        if op not in self._simplifiers:
            return None
        return self._simplifiers[op](*args)

    @staticmethod
    def _deduplicate_filter(args):
        seen = set()
        new_args = []
        for arg in args:
            key = arg.cache_key
            if key in seen:
                continue
            seen.add(key)
            new_args.append(arg)
        return new_args

    #
    # The simplifiers.
    #

    # pylint:disable=inconsistent-return-statements

    @staticmethod
    def if_simplifier(cond, if_true, if_false):
        # NOTE: this is never called; simplifications are implemented inline in the If op. why?
        if cond.is_true():
            return if_true

        if cond.is_false():
            return if_false

    @staticmethod
    def concat_simplifier(*args):
        if len(args) == 1:
            return args[0]

        orig_args = args
        args = list(args)
        # length = sum(arg.length for arg in args)
        simplified = False

        if any(a.symbolic for a in args):
            i = 1
            # here, we concatenate any consecutive concrete terms
            while i < len(args):
                previous = args[i - 1]
                current = args[i]

                if (
                    not (previous.symbolic or current.symbolic)
                    and backends.concrete.handles(previous)
                    and backends.concrete.handles(current)
                ):
                    concatted = ast.all_operations.Concat(previous, current)
                    # If the concrete arguments to concat have non-relocatable annotations attached,
                    # we may not be able to simplify the concrete concat. This check makes sure we don't
                    # create a nested concat in that case.
                    #
                    # This is necessary to ensure that simplified is set correctly. If we don't check this here,
                    # later the concat-of-concat will eliminate the newly introduced concat again, meaning we end
                    # up with the same args that we started with. But because we only eliminate the concat later,
                    # the simplified variable would still be set to True after this loop which is wrong.
                    if concatted.op != "Concat":
                        args[i - 1 : i + 1] = (concatted,)
                        continue

                i += 1

            if len(args) < len(orig_args):
                simplified = True

        # here, we flatten any concats among the arguments and remove zero-length arguments
        i = 0
        while i < len(args):
            current = args[i]
            if current.length == 0:
                args.pop(i)
                simplified = True
            elif current.op == "Concat":
                simplified = True
                args[i : i + 1] = current.args
                i += len(current.args)
            else:
                i += 1

        # here, we consolidate any consecutive concats on extracts from the same variable
        i = 0
        prev_var = None
        prev_left = None
        prev_right = None
        while i < len(args):
            if args[i].op != "Extract":
                prev_var = None
                prev_left = None
                prev_right = None
                i += 1
            elif prev_var is args[i].args[2] and prev_right == args[i].args[0] + 1:
                prev_right = args[i].args[1]
                args[i - 1 : i + 1] = [ast.all_operations.Extract(prev_left, prev_right, prev_var)]
                simplified = True
            else:
                prev_left = args[i].args[0]
                prev_right = args[i].args[1]
                prev_var = args[i].args[2]
                i += 1

        # if any(a.op == 'Reverse' for a in args):
        # 	  simplified = True
        # 	  args = [a.reversed for a in args]

        if simplified:
            return ast.all_operations.Concat(*args)

        return

    @staticmethod
    def rshift_simplifier(val, shift):
        if (shift == 0).is_true():
            return val
        if val.op == "Concat" and (val.args[0] == 0).is_true() and (shift > val.size() - val.args[0].size()).is_true():
            return ast.all_operations.BVV(0, val.size())
        if val.op == "ZeroExt" and (shift > val.size() - val.args[0]).is_true():
            return ast.all_operations.BVV(0, val.size())

    @staticmethod
    def lshr_simplifier(val, shift):
        if (shift == 0).is_true():
            return val
        if val.op == "Concat" and (val.args[0] == 0).is_true() and (shift > val.size() - val.args[0].size()).is_true():
            return ast.all_operations.BVV(0, val.size())
        if val.op == "ZeroExt" and (shift > val.size() - val.args[0]).is_true():
            return ast.all_operations.BVV(0, val.size())

    @staticmethod
    def lshift_simplifier(val, shift):
        if (shift == 0).is_true():
            return val
        if val.op == "__lshift__":
            real_val, inner_shift = val.args
            return real_val << (inner_shift + shift)

    @staticmethod
    def eq_simplifier(a, b):
        if a is b:
            return ast.true

        if isinstance(a, ast.Bool) and b is ast.true:
            return a
        if isinstance(b, ast.Bool) and a is ast.true:
            return b
        if isinstance(a, ast.Bool) and b is ast.false:
            return ast.all_operations.Not(a)
        if isinstance(b, ast.Bool) and a is ast.false:
            return ast.all_operations.Not(b)

        if a.op == "Reverse" and b.op == "Reverse":
            return a.args[0] == b.args[0]

        # simple canonicalization
        if a.op == "BVV" and b.op != "BVV":
            return b == a

        # expr - c1 == c2    ->   expr == c1 + c2
        if a.op == "__sub__" and len(a.args) == 2 and a.args[1].op == "BVV" and b.op == "BVV":
            return a.args[0] == a.args[1] + b

        # 1 ^ expr == 0     ->   expr == 1
        if a.op == "__xor__" and b.op == "BVV" and b.args[0] == 0 and len(a.args) == 2:
            if a.args[1].op == "BVV" and a.args[1].args[0] == 1:  # expr ^ 1 == 0
                return a.args[0] == 1
            elif a.args[0].op == "BVV" and a.args[0].args[0] == 1:  # 1 ^ expr == 0
                return a.args[1] == 1

        # TODO: all these ==/!= might really slow things down...
        if a.op == "If":
            if a.args[1] is b and ast.all_operations.is_true(a.args[2] != b):
                # (If(c, x, y) == x, x != y) -> c
                return a.args[0]
            elif a.args[2] is b and ast.all_operations.is_true(a.args[1] != b):
                # (If(c, x, y) == y, x != y) -> !c
                return ast.all_operations.Not(a.args[0])
            # elif a._claripy.is_true(a.args[1] == b) and a._claripy.is_true(a.args[2] == b):
            # 	  return a._claripy.true
            # elif a._claripy.is_true(a.args[1] != b) and a._claripy.is_true(a.args[2] != b):
            # 	  return a._claripy.false

        if b.op == "If":
            if b.args[1] is a and ast.all_operations.is_true(b.args[2] != b):
                # (x == If(c, x, y)) -> c
                return b.args[0]
            elif b.args[2] is a and ast.all_operations.is_true(b.args[1] != a):
                # (y == If(c, x, y)) -> !c
                return ast.all_operations.Not(b.args[0])
            # elif b._claripy.is_true(b.args[1] == a) and b._claripy.is_true(b.args[2] == a):
            # 	  return b._claripy.true
            # elif b._claripy.is_true(b.args[1] != a) and b._claripy.is_true(b.args[2] != a):
            # 	  return b._claripy.false

        # Masking and comparing against a constant
        simp = SimplificationManager.and_mask_comparing_against_constant_simplifier(operator.__eq__, a, b)
        if simp is not None:
            return simp

        # ZeroExt/Concat and Extract and comparing against a constant
        simp = SimplificationManager.zeroext_extract_comparing_against_constant_simplifier(operator.__eq__, a, b)
        if simp is not None:
            return simp

        # ZeroExt/Concat and comparing against a constant
        simp = SimplificationManager.zeroext_comparing_against_simplifier(operator.__eq__, a, b)
        if simp is not None:
            return simp

        if (a.op in SIMPLE_OPS or b.op in SIMPLE_OPS) and a.length > 1 and a.length == b.length:
            for i in range(a.length):
                a_bit = a[i:i]
                if a_bit.symbolic:
                    break

                b_bit = b[i:i]
                if b_bit.symbolic:
                    break

                if ast.all_operations.is_false(a_bit == b_bit):
                    return ast.all_operations.false

    @staticmethod
    def ne_simplifier(a, b):
        if a is b:
            return ast.false

        if a.op == "Reverse" and b.op == "Reverse":
            return a.args[0] != b.args[0]

        if a.op == "If":
            if a.args[2] is b and ast.all_operations.is_true(a.args[1] != b):
                # (If(c, x, y) == x, x != y) -> c
                return a.args[0]
            elif a.args[1] is b and ast.all_operations.is_true(a.args[2] != b):
                # (If(c, x, y) == y, x != y) -> !c
                return ast.all_operations.Not(a.args[0])
            # elif a._claripy.is_true(a.args[1] == b) and a._claripy.is_true(a.args[2] == b):
            # 	  return a._claripy.false
            # elif a._claripy.is_true(a.args[1] != b) and a._claripy.is_true(a.args[2] != b):
            # 	  return a._claripy.true

        if b.op == "If":
            if b.args[2] is a and ast.all_operations.is_true(b.args[1] != a):
                # (x == If(c, x, y)) -> c
                return b.args[0]
            elif b.args[1] is a and ast.all_operations.is_true(b.args[2] != a):
                # (y == If(c, x, y)) -> !c
                return ast.all_operations.Not(b.args[0])
            # elif b._claripy.is_true(b.args[1] != a) and b._claripy.is_true(b.args[2] != a):
            # 	  return b._claripy.true
            # elif b._claripy.is_true(b.args[1] == a) and b._claripy.is_true(b.args[2] == a):
            # 	  return b._claripy.false

        # 1 ^ expr != 0     ->   expr == 0
        if a.op == "__xor__" and b.op == "BVV" and b.args[0] == 0 and len(a.args) == 2:
            if a.args[1].op == "BVV" and a.args[1].args[0] == 1:
                return a.args[0] != 1
            elif a.args[0].op == "BVV" and a.args[0].args[0] == 1:
                return a.args[1] != 1

        # Masking and comparing against a constant
        simp = SimplificationManager.and_mask_comparing_against_constant_simplifier(operator.__ne__, a, b)
        if simp is not None:
            return simp

        # ZeroExt/Concat and Extract and comparing against a constant
        simp = SimplificationManager.zeroext_extract_comparing_against_constant_simplifier(operator.__ne__, a, b)
        if simp is not None:
            return simp

        # ZeroExt/Concat and comparing against a constant
        simp = SimplificationManager.zeroext_comparing_against_simplifier(operator.__ne__, a, b)
        if simp is not None:
            return simp

        if (a.op == SIMPLE_OPS or b.op in SIMPLE_OPS) and a.length > 1 and a.length == b.length:
            for i in range(a.length):
                a_bit = a[i:i]
                if a_bit.symbolic:
                    break

                b_bit = b[i:i]
                if b_bit.symbolic:
                    break

                if ast.all_operations.is_true(a_bit != b_bit):
                    return ast.all_operations.true

    @staticmethod
    def ge_simplifier(a, b):
        # ZeroExt/Concat and comparing against a constant
        simp = SimplificationManager.zeroext_comparing_against_simplifier(operator.__ge__, a, b)
        if simp is not None:
            return simp

    @staticmethod
    def bv_reverse_simplifier(body):
        if body.op == "Reverse":
            # Reverse(Reverse(x)) ==> x
            return body.args[0]

        if body.length == 8:
            # Reverse(byte) ==> byte
            return body

        if body.op == "Concat":
            if all(a.op == "Extract" for a in body.args):
                first_ast = body.args[0].args[2]
                for i, a in enumerate(body.args):
                    if not (first_ast is a.args[2] and a.args[0] == ((i + 1) * 8 - 1) and a.args[1] == i * 8):
                        break
                else:
                    upper_bound = body.args[-1].args[0]
                    if first_ast.length == upper_bound + 1:
                        return first_ast
                    else:
                        return first_ast[upper_bound:0]
            if all(a.length == 8 for a in body.args):
                return body.make_like(body.op, body.args[::-1], simplify=True)

        if (
            body.op == "Concat"
            and all(a.op == "Reverse" for a in body.args)
            and all(a.length % 8 == 0 for a in body.args)
        ):
            return body.make_like(body.op, [a.args[0] for a in reversed(body.args)], simplify=True)

        if body.op == "Extract" and body.args[2].op == "Reverse":
            # Reverse(Extract(hi, lo, Reverse(x))) ==> Extract(bits-lo-1, bits-hi-1, x)
            # Holds only when (hi+1) and lo are multiples of 8 (or, multiples of bits_per_byte if we really want to
            # suppport cLEMENCy)
            hi, lo = body.args[0:2]
            if (hi + 1) % 8 == 0 and lo % 8 == 0:
                x = body.args[2].args[0]
                new_hi = x.size() - lo - 1
                new_lo = x.size() - hi - 1
                return body.make_like(body.op, (new_hi, new_lo, x), simplify=True)

    @staticmethod
    def boolean_and_simplifier(*args):
        if len(args) == 1:
            return args[0]

        new_args = [None] * len(args)
        ctr = 0
        for a in args:
            if a.op == "BoolV":
                if a.is_false():
                    return ast.all_operations.false
            else:
                new_args[ctr] = a
                ctr += 1
        new_args = new_args[:ctr]

        if not new_args:
            return ast.true

        if len(new_args) < len(args):
            return ast.all_operations.And(*new_args)

        # a >= c && a != c    ->   a>c
        if len(args) == 2:
            a = args[0]
            b = args[1]
            if (
                len(a.args) >= 2
                and len(b.args) >= 2
                and a.args[0] is b.args[0]
                and a.args[1] is b.args[1]
                and a.op == "__ge__"
                and b.op == "__ne__"
            ):
                return ast.all_operations.UGT(a.args[0], a.args[1])

        flattened = SimplificationManager._flatten_simplifier("And", SimplificationManager._deduplicate_filter, *args)
        if flattened is None:
            return None

        if flattened.op != "And":
            return flattened

        fargs = flattened.args

        # Check if we are left with one argument again
        if len(fargs) == 1:
            return fargs[0]

        # what the fuck is this supposed to do?
        if any(len(arg.args) != 2 for arg in fargs):
            return flattened

        target_var = None

        # Determine the unknown variable
        if fargs[0].args[0].symbolic and (fargs[0].args[0] is fargs[1].args[0] or fargs[0].args[0] is fargs[1].args[1]):
            target_var = fargs[0].args[0]
        elif fargs[0].args[1].symbolic and (
            fargs[0].args[1] is fargs[1].args[0] or fargs[0].args[1] is fargs[1].args[1]
        ):
            target_var = fargs[0].args[1]

        if target_var is None:
            return flattened

        # we now know that the And is a series of binary conditions over a single variable.
        # we can optimize accordingly.
        # right now it's just check for eq/ne

        eq_list = []
        ne_list = []
        for arg in fargs:
            other = arg.args[1] if arg.args[0] is target_var else arg.args[0] if arg.args[1] is target_var else None
            if other is None:
                return flattened
            if arg.op == "__eq__":
                eq_list.append(other)
            elif arg.op == "__ne__":
                ne_list.append(other)
            else:
                return flattened

        if not eq_list:
            return flattened
        if any(any(ne is eq for eq in eq_list) for ne in ne_list):
            return ast.all_operations.false
        if all(v.op == "BVV" for v in eq_list) and all(v.op == "BVV" for v in ne_list):
            mustbe = eq_list[0]
            if any(eq.args[0] != mustbe.args[0] for eq in eq_list):
                return ast.all_operations.false
            return target_var == eq_list[0]
        return flattened

    @staticmethod
    def boolean_or_simplifier(*args):
        if len(args) == 1:
            return args[0]

        new_args = []
        for a in args:
            if a.is_true():
                return ast.all_operations.true
            elif not a.is_false():
                new_args.append(a)

        if not new_args:
            return ast.false
        if len(new_args) < len(args):
            return ast.all_operations.Or(*new_args)

        return SimplificationManager._flatten_simplifier("Or", SimplificationManager._deduplicate_filter, *args)

    @staticmethod
    def _flatten_simplifier(op_name, filter_func, *args, **kwargs):
        # we cannot further flatten if any top-level argument has non-relocatable annotations
        if any(not anno.relocatable for anno in itertools.chain.from_iterable(arg.annotations for arg in args)):
            return None

        new_args = tuple(
            itertools.chain.from_iterable(
                (a.args if isinstance(a, ast.Base) and a.op == op_name and len(a.args) < 1000 else (a,)) for a in args
            )
        )

        # try to collapse multiple concrete args
        value_args = []
        other_args = []
        for arg in new_args:
            if getattr(arg, "op", None) == "BVV":
                value_args.append(arg)
            else:
                other_args.append(arg)
        if other_args and len(value_args) > 1:
            value_arg = value_args[0].make_like(op_name, tuple(value_args), simplify=False)
            new_args = (*tuple(other_args), value_arg)

        variables = frozenset(itertools.chain.from_iterable(a.variables for a in args if isinstance(a, ast.Base)))
        if filter_func:
            new_args = filter_func(new_args)
        if not new_args and "initial_value" in kwargs:
            return kwargs["initial_value"]
        # if a single arg is left, don't create an op for it
        if len(new_args) == 1:
            return new_args[0]
        return next(a for a in args if isinstance(a, ast.Base)).make_like(
            op_name, new_args, variables=variables, simplify=False
        )

    @staticmethod
    def bitwise_add_simplifier(*args):
        if len(args) == 2 and args[1].op == "BVV" and args[0].op == "__sub__" and args[0].args[1].op == "BVV":
            # flatten add over sub
            # (x - y) + z ==> x - (y - z)
            return args[0].args[0] - (args[0].args[1] - args[1])
        return SimplificationManager._flatten_simplifier(
            "__add__",
            lambda new_args: tuple(a for a in new_args if a.op != "BVV" or a.args[0] != 0),
            *args,
            initial_value=ast.all_operations.BVV(0, len(args[0])),
        )
        return None

    @staticmethod
    def bitwise_mul_simplifier(*args):
        return SimplificationManager._flatten_simplifier("__mul__", None, *args)

    @staticmethod
    def bitwise_sub_simplifier(a, b):
        if b.op == "BVV":
            # many optimizations if b is concrete - effectively flattening
            if b.args[0] == 0:
                return a
            elif a.op == "__sub__" and a.args[1].op == "BVV":
                # flatten right-heavy trees
                # (x - y) - z ==> x - (y + z)
                return a.args[0] - (a.args[1] + b)
            elif a.op == "__add__" and a.args[-1].op == "BVV":
                # flatten sub over add
                # (x + y) - z ==> x + (y - z)
                if len(a.args) == 2:
                    return a.args[0] + (a.args[-1] - b)
                else:
                    return a.swap_args(a.args[:-1] + (a.args[-1] - b,))
        elif a is b or (a == b).is_true():
            return ast.all_operations.BVV(0, a.size())
        return None

    # recognize b-bit z=signedmax(q,r) from this idiom:
    # s=q-r;t=q^r;u=s^q;v=u&t;w=v^s;x=rshift(w,b-1);y=x&t;z=q^y
    # and recognize b-bit z=signedmin(q,r) from this idiom:
    # s=r-q;t=q^r;u=s^r;v=u&t;w=v^s;x=rshift(w,b-1);y=x&t;z=q^y
    @staticmethod
    def bitwise_xor_simplifier_minmax(a, b):
        q, y = a, b
        if y.op != "__and__":
            q, y = b, a
            if y.op != "__and__":
                return

        if len(y.args) != 2:
            return
        x, t = y.args
        if t.op != "__xor__":
            t, x = y.args
            if t.op != "__xor__":
                return

        if x.op != "__rshift__":
            return
        w, dist = x.args

        bits = a.size()
        if dist is not ast.all_operations.BVV(bits - 1, bits):
            return
        if w.op != "__xor__":
            return

        if len(w.args) != 2:
            return
        v, s = w.args
        if s.op != "__sub__":
            s, v = w.args
            if s.op != "__sub__":
                return

        if v.op != "__and__":
            return
        if len(v.args) != 2:
            return
        u, t2 = v.args
        if t2 is not t:
            t2, u = v.args
            if t2 is not t:
                return

        if u.op != "__xor__":
            return

        if len(t.args) != 2:
            return
        q2, r = t.args
        if q2 is not q:
            r, q2 = t.args
            if q2 is not q:
                return

        if (u.args[0] is s and u.args[1] is q) or (u.args[0] is q and u.args[1] is s):
            if not (s.args[0] is q and s.args[1] is r):
                return
            cond = ast.all_operations.SLE(q, r)
            return ast.all_operations.If(cond, r, q)

        if (u.args[0] is s and u.args[1] is r) or (u.args[0] is r and u.args[1] is s):
            if not (s.args[0] is r and s.args[1] is q):
                return
            cond = ast.all_operations.SLE(q, r)
            return ast.all_operations.If(cond, q, r)

    @staticmethod
    def bitwise_xor_simplifier(a, b, *args):
        if not args:
            if a is ast.all_operations.BVV(0, a.size()):
                return b
            elif b is ast.all_operations.BVV(0, a.size()):
                return a
            elif a is b or (a == b).is_true():
                return ast.all_operations.BVV(0, a.size())

            result = SimplificationManager.bitwise_xor_simplifier_minmax(a, b)
            if result is not None:
                return result

        def _flattening_filter(args):
            # since a ^ a == 0, we can safely remove those from args
            # this procedure is done carefully in order to keep the ordering of arguments
            ctr = collections.Counter(arg.cache_key for arg in args)
            res = []
            seen = set()
            for arg in args:
                if ctr[arg.cache_key] % 2 == 0:
                    continue
                l1 = len(seen)
                seen.add(arg.cache_key)
                l2 = len(seen)
                if l1 != l2:
                    res.append(arg)
            return tuple(res)

        return SimplificationManager._flatten_simplifier(
            "__xor__",
            _flattening_filter,
            a,
            b,
            *args,
            initial_value=ast.all_operations.BVV(0, a.size()),
        )

    @staticmethod
    def bitwise_or_simplifier(a, b, *args):
        if not args:
            if a is ast.all_operations.BVV(0, a.size()):
                return b
            if b is ast.all_operations.BVV(0, a.size()):
                return a
            if a.op == b.op and a.op in {"BVV", "BoolV", "FPV"}:
                if a.args == b.args and (a == b).is_true():
                    return a
            elif (a == b).is_true():
                return a
            if a is b:
                return a

        return SimplificationManager._flatten_simplifier(
            "__or__", SimplificationManager._deduplicate_filter, a, b, *args
        )

    @staticmethod
    def bitwise_and_simplifier(a, b, *args):
        if not args:
            # try to perform a rotate-shift-mask simplification
            r = SimplificationManager.rotate_shift_mask_simplifier(a, b)
            if r is not None:
                return r
            # we do not use (a == 2 ** a.size()-1).is_true() to avoid creating redundant ASTs
            if a.op == "BVV" and a.args[0] == 2 ** a.size() - 1:
                return b
            if b.op == "BVV" and b.args[0] == 2 ** b.size() - 1:
                return a
            if a is b:
                return a
            # for concrete values, we delay the AST creation as much as possible
            if a.op == b.op and a.op in {"BVV", "BoolV", "FPV"}:
                if a.args == b.args and (a == b).is_true():
                    return a
            elif (a == b).is_true():
                return a
            if a.op == "BVV" and a.args[0] == 0:
                return ast.all_operations.BVV(0, a.size())
            if b.op == "BVV" and b.args[0] == 0:
                return ast.all_operations.BVV(0, a.size())
            # Concat(a.args[0], a.args[1]) & b  ==>  ZeroExt(size, a.args[1])
            # maybe we can drop the second argument
            if a.op == "Concat" and len(a.args) == 2 and (b == 2 ** (a.size() - a.args[0].size()) - 1).is_true():
                # yes!
                return ast.all_operations.ZeroExt(a.args[0].size(), a.args[1])

            # if(cond0, 1, 0) & if(cond1, 1, 0)  ->  if(cond0 & cond1, 1, 0)
            if (
                a.op == "If"
                and b.op == "If"
                and (
                    (a.args[1] == ast.all_operations.BVV(1, 1)).is_true()
                    and (a.args[2] == ast.all_operations.BVV(0, 1)).is_true()
                    and (b.args[1] == ast.all_operations.BVV(1, 1)).is_true()
                    and (b.args[2] == ast.all_operations.BVV(0, 1)).is_true()
                )
            ):
                cond0 = a.args[0]
                cond1 = b.args[0]
                return ast.all_operations.If(
                    cond0 & cond1,
                    ast.all_operations.BVV(1, 1),
                    ast.all_operations.BVV(0, 1),
                )

        return SimplificationManager._flatten_simplifier(
            "__and__", SimplificationManager._deduplicate_filter, a, b, *args
        )

    @staticmethod
    def boolean_not_simplifier(body):
        if body.op == "__eq__":
            return body.args[0] != body.args[1]
        elif body.op == "__ne__":
            return body.args[0] == body.args[1]

        if body.op == "Not":
            return body.args[0]

        if body.op == "SLT":
            return ast.all_operations.SGE(body.args[0], body.args[1])
        elif body.op == "SLE":
            return ast.all_operations.SGT(body.args[0], body.args[1])
        elif body.op == "SGT":
            return ast.all_operations.SLE(body.args[0], body.args[1])
        elif body.op == "SGE":
            return ast.all_operations.SLT(body.args[0], body.args[1])

        if body.op == "ULT":
            return ast.all_operations.UGE(body.args[0], body.args[1])
        elif body.op == "ULE":
            return ast.all_operations.UGT(body.args[0], body.args[1])
        elif body.op == "UGT":
            return ast.all_operations.ULE(body.args[0], body.args[1])
        elif body.op == "UGE":
            return ast.all_operations.ULT(body.args[0], body.args[1])

        if body.op == "__lt__":
            return ast.all_operations.UGE(body.args[0], body.args[1])
        elif body.op == "__le__":
            return ast.all_operations.UGT(body.args[0], body.args[1])
        elif body.op == "__gt__":
            return ast.all_operations.ULE(body.args[0], body.args[1])
        elif body.op == "__ge__":
            return ast.all_operations.ULT(body.args[0], body.args[1])

    @staticmethod
    def zeroext_simplifier(n, e):
        if n == 0:
            return e

        if e.op == "ZeroExt":
            # ZeroExt(A, ZeroExt(B, x)) ==> ZeroExt(A + B, x)
            return e.make_like(e.op, (n + e.args[0], e.args[1]), length=n + e.size(), simplify=True)

    @staticmethod
    def signext_simplifier(n, e):
        if n == 0:
            return e

        # TODO: if top bit is 0, do a zero-extend instead

    @staticmethod
    def extract_simplifier(high, low, val):
        # if we're extracting the whole value, return the value
        if high - low + 1 == val.size():
            return val

        if (val.op == "SignExt" or val.op == "ZeroExt") and low == 0 and high + 1 == val.args[1].size():
            return val.args[1]

        if val.op == "ZeroExt":
            extending_bits = val.args[0]
            if extending_bits == 0:
                val = val.args[1]
            else:
                val = ast.all_operations.Concat(ast.all_operations.BVV(0, extending_bits), val.args[1])

        # Reverse(concat(a, b)) -> concat(Reverse(b), Reverse(a))
        # a and b must have lengths that are a multiple of 8
        if val.op == "Reverse" and val.args[0].op == "Concat" and all(a.length % 8 == 0 for a in val.args[0].args):
            val = ast.all_operations.Concat(*reversed([a.reversed for a in val.args[0].args]))

        # Reading one byte from a reversed ast can be converted to reading the corresponding byte from the original ast
        # No Reverse is required then
        if val.op == "Reverse" and high - low + 1 == 8 and low % 8 == 0:
            byte_pos = low // 8
            new_byte_pos = val.length // 8 - byte_pos - 1

            val = val.args[0]
            high = (new_byte_pos + 1) * 8 - 1
            low = new_byte_pos * 8

            return ast.all_operations.Extract(high, low, val)

        if val.op == "Concat":
            pos = val.length
            high_i, low_i, high_loc, low_loc = None, None, None, None
            for i, v in enumerate(val.args):
                if pos - v.length <= high < pos:
                    high_i = i
                    high_loc = high - (pos - v.length)
                if pos - v.length <= low < pos:
                    low_i = i
                    low_loc = low - (pos - v.length)
                pos -= v.length

            used = list(val.args[high_i : low_i + 1])

            # if we have only one part, we can avoid creating a new concat
            if len(used) == 1:
                new_high = low_loc + high - low
                result = used[0]

                # avoid extracting if we need the full value
                if new_high == result.length - 1 and low_loc == 0:
                    return result

                # else extract the part we need
                return result[new_high:low_loc]

            # if we have more than one part, cut the parts that we need from the start & end chunks
            # if necessary
            if high_loc != used[0].length:
                used[0] = used[0][high_loc:]

            if low_loc != 0:
                used[-1] = used[-1][:low_loc]

            return ast.all_operations.Concat(*used)

        if val.op == "Extract":
            _, inner_low = val.args[:2]
            new_low = inner_low + low
            new_high = new_low + (high - low)
            return (val.args[2])[new_high:new_low]

        if val.op == "Reverse" and val.args[0].op == "Concat" and all(a.length % 8 == 0 for a in val.args[0].args):
            val = val.make_like(
                "Concat",
                tuple(reversed([a.reversed for a in val.args[0].args])),
                simplify=True,
            )[high:low]
            if not val.symbolic:
                return val

        # if all else fails, convert Extract(Reverse(...)) to Reverse(Extract(...))
        # if val.op == 'Reverse' and (high + 1) % 8 == 0 and low % 8 == 0:
        # 	  print("saw reverse, converting")
        # 	  inner_length = val.args[0].length
        # 	  try:
        # 		  return val.args[0][(inner_length - 1 - low):(inner_length - 1 - low - (high - low))].reversed
        # 	  except ClaripyOperationError:
        # 		  __import__('ipdb').set_trace()

        if val.op in extract_distributable:
            all_args = tuple(a[high:low] for a in val.args)
            if val.op in flattenable:
                # directly create a flattened AST
                return next(a for a in all_args if isinstance(a, ast.Base)).make_like(val.op, all_args)
            else:
                return reduce(getattr(operator, val.op), all_args)

        #  (if cond then 1 else 0)[0:0]  ->  if(cond then 1[0:0] else 0[0:0])
        if val.op == "If":
            ifcond, iftrue, iffalse = val.args
            if iftrue.op == "BVV" and iffalse.op == "BVV":
                # extract from iftrue and iffalse
                return ast.bool.If(ifcond, iftrue[high:low], iffalse[high:low])

        # invert(expr)[0:0]   ->   invert(expr[0:0])
        if val.op == "__invert__":
            return ast.BV.__invert__(val.args[0][high:low])

    # oh gods
    @staticmethod
    def fptobv_simplifier(the_fp):
        if the_fp.op == "fpToFP" and len(the_fp.args) == 2:
            return the_fp.args[0]

    @staticmethod
    def fptofp_simplifier(*args):
        if len(args) == 2 and args[0].op == "fpToIEEEBV":
            to_bv, sort = args
            if (sort == fp.FSORT_FLOAT and to_bv.length == 32) or (sort == fp.FSORT_DOUBLE and to_bv.length == 64):
                return to_bv.args[0]

    @staticmethod
    def rotate_shift_mask_simplifier(a, b):
        """
        Handles the following case:
            ((A << a) | (A >> (_N - a))) & mask, where
                A being a BVS,
                a being a integer that is less than _N,
                _N is either 32 or 64, and
                mask can be evaluated to 0xffffffff (64-bit) or 0xffff (32-bit) after reversing the rotate-shift
                operation.

        It will be simplified to:
            (A & (mask >>> a)) <<< a
        """

        # is the second argument a BVV?
        if b.op != "BVV":
            return None

        # is it a rotate-shift?
        if a.op != "__or__" or len(a.args) != 2:
            return None
        a_0, a_1 = a.args

        if a_0.op != "__lshift__":
            return None
        if a_1.op != "LShR":
            return None
        a_00, a_01 = a_0.args
        a_10, a_11 = a_1.args
        if a_00 is not a_10:
            return None
        if a_01.op != "BVV" or a_11.op != "BVV":
            return None
        lshift_ = a_01.args[0]
        rshift_ = a_11.args[0]
        bitwidth = lshift_ + rshift_
        if bitwidth not in (32, 64):
            return None

        # is the second argument a mask?
        # Note: the following check can be further loosen if we want to support more masks.
        if bitwidth == 32:
            m = ((b.args[0] << rshift_) & 0xFFFFFFFF) | (b.args[0] >> lshift_)
            if m != 0xFFFF:
                return None
        else:  # bitwidth == 64
            m = ((b.args[0] << rshift_) & 0xFFFFFFFFFFFFFFFF) | (b.args[0] >> lshift_)
            if m != 0xFFFFFFFF:
                return None

        # Show our power!
        masked_a = a_00 & m
        expr = (masked_a << lshift_) | (masked_a >> rshift_)
        return expr

    @staticmethod
    def str_reverse_simplifier(arg):
        return arg

    @staticmethod
    def invert_simplifier(expr):
        # ~ if(cond then 1 else 0)  ->  if(cond, ~1, ~0)  ->    if(!cond, 1,0)
        if expr.op == "If" and expr.args[1].op == "BVV" and expr.args[1].args[0] == 1 and expr.args[2].args[0] == 0:
            return ast.bool.If(ast.all_operations.Not(expr.args[0]), expr.args[1], expr.args[2])

    @staticmethod
    def and_mask_comparing_against_constant_simplifier(op, a, b):
        """
        This simplifier handles the following case:

            A & mask == b, and
            A & mask != b

        If the high bits of A are 0, `& mask` can be eliminated.
        """
        if op in (operator.__eq__, operator.__ne__) and a.op == "__and__" and len(a.args) == 2 and b.op == "BVV":
            a_arg0, a_arg1 = a.args
            if a_arg1.op == "BVV":
                # it's a constant mask
                # check if the higher bits are 0
                v = a_arg1.args[0]
                zero_bits = a_arg1.args[1]
                mask_allones = True
                while v != 0:
                    mask_allones = mask_allones and ((v & 1) == 0)
                    v = v >> 1
                    zero_bits -= 1
                if zero_bits > 0:
                    # the high `zero_bits` bits are zero
                    # check the constant
                    b_higher = b[b.size() - 1 : b.size() - zero_bits]
                    b_higher_bits_are_0: bool | None = None
                    if (b_higher == 0).is_true():
                        b_higher_bits_are_0 = True
                    elif (b_higher == 0).is_false():
                        b_higher_bits_are_0 = False

                    if b_higher_bits_are_0 is True:
                        # extra check: can we get rid of the mask
                        if zero_bits == b.size():
                            # the mask is 0, which means the left-hand side becomes 0 after masking
                            return op(ast.all_operations.BVV(0, b.size()), b)

                        b_highbit_idx = b.size() - 1 - zero_bits
                        # originally, b was 8-bit aligned. Can we keep the size of the new expression 8-byte aligned?
                        if b.size() % 8 == 0 and (b_highbit_idx + 1) % 8 != 0:
                            b_highbit_idx += 8 - (b_highbit_idx + 1) % 8
                        b_lower = b[b_highbit_idx:0]
                        if mask_allones:
                            # yes!
                            return op(a_arg0[b_highbit_idx:0], b_lower)
                        else:
                            # nope
                            if b_highbit_idx == b.size() - 1:
                                # no change is happening
                                return None
                            return op(a_arg0[b_highbit_idx:0] & a_arg1.args[0], b_lower)
                    elif b_higher_bits_are_0 is False:
                        return ast.all_operations.false if op is operator.__eq__ else ast.all_operations.true

        return None

    @staticmethod
    def zeroext_extract_comparing_against_constant_simplifier(op, a, b):
        """
        This simplifier handles the following cases:

            Extract(hi, 0, Concat(0, A)) op b, and
            Extract(hi, 0, ZeroExt(n, A)) op b

        Extract can be eliminated if the high bits of Concat(0, A) or ZeroExt(n, A) are all zeros.
        """

        # TODO: This method is only used when op is __eq__ or __ne__. We need more experiment to see if it is necessary
        # TODO: to apply this optimization to other comparison operators.

        if a.op != "Extract" or a.args[1] != 0:
            return None

        highbits_are_zeros = False

        a_hi, _, a_arg = a.args
        a_inner_expr = None
        if a_arg.op == "Concat" and len(a_arg.args) == 2:
            a_concat_expr0 = a_arg.args[0]
            a_inner_expr = a_arg.args[1]
            # equivalent to ZeroExt
            if (
                a_concat_expr0.op == "BVV"
                and a_concat_expr0.args[0] == 0
                and a_concat_expr0.size() >= a_arg.size() - a_hi
            ):
                # high bits are all zeros
                highbits_are_zeros = True

        elif a_arg.op == "ZeroExt":
            a_zeroext_bits = a_arg.args[0]
            a_inner_expr = a_arg.args[1]
            if a_zeroext_bits >= a_arg.size() - a_hi:
                # high bits are all zeros
                highbits_are_zeros = True

        if highbits_are_zeros:
            to_extend = b.size() - a_inner_expr.size()
            if to_extend == 0:
                return op(a_inner_expr, b)
            else:
                return op(ast.all_operations.ZeroExt(to_extend, a_inner_expr), b)

        return None

    @staticmethod
    def zeroext_comparing_against_simplifier(op, a, b):
        """
        This simplifier handles the following cases:

            ZeroExt(n, A) == b,
            ZeroExt(n, A) != b, and
            ZeroExt(n, A) >= b

        If the high bits of b are all zeros (in case of ==, !=, and >=) or have at least one ones (in case of !=),
        ZeroExt can be eliminated.
        """
        if op in {operator.__eq__, operator.__ne__, operator.__ge__} and b.op == "BVV":
            if a.op == "ZeroExt":
                # check if the high bits of b are zeros
                a_zeroext_bits = a.args[0]
                b_highbits = b[b.size() - 1 : b.size() - a_zeroext_bits]
                if (b_highbits == 0).is_true():
                    # we can get rid of ZeroExt
                    return op(a.args[1], b[b.size() - a_zeroext_bits - 1 : 0])
                elif (b_highbits == 0).is_false():
                    # unsat
                    return ast.all_operations.false if op is operator.__eq__ else ast.all_operations.true

            if (
                a.op == "Concat" and len(a.args) == 2 and a.args[0].op == "BVV" and a.args[0].args[0] == 0
            ):  # make sure high bits of a are zeros
                a_zero_bits = a.args[0].args[1]
                b_highbits = b[b.size() - 1 : b.size() - a_zero_bits]
                if (b_highbits == 0).is_true():
                    # we can get rid of Concat
                    return op(a.args[1], b[b.size() - a_zero_bits - 1 : 0])
                elif (b_highbits == 0).is_false():
                    # unsat
                    return ast.all_operations.false if op is operator.__eq__ else ast.all_operations.true

        return None


SIMPLE_OPS = ("Concat", "SignExt", "ZeroExt")

extract_distributable = {
    "__and__",
    "__rand__",
    "__or__",
    "__ror__",
    "__xor__",
    "__rxor__",
}

flattenable = {
    "__and__",
    "__or__",
    "__xor__",
    "__mul__",
    "And",
    "Or",
}


# the actual instance
simpleton = SimplificationManager()
