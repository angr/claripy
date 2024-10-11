from __future__ import annotations

import claripy


def vsa_union_simplifier(a, b):
    if a.op == "BVSet" and b.op == "BVSet":
        # TODO: collapsing logic
        return claripy.ast.bvset.BVSet("BVSet", a.bits, a.args[2] | b.args[2])
    return None


def vsa_intersection_simplifier(a, b):
    # TODO
    return None


def vsa_widen_simplifier(a, b):
    # TODO
    return None


def vsa_add_simplifier(a, b):
    # TODO
    return None


def vsa_sub_simplifier(a, b):
    # TODO
    return None


def vsa_mul_simplifier(a, b):
    # TODO
    return None


def vsa_mod_simplifier(a, b):
    # TODO
    return None


def vsa_and_simplifier(a, b):
    # TODO
    return None


def vsa_or_simplifier(a, b):
    # TODO
    return None


def vsa_xor_simplifier(a, b):
    # TODO
    return None


def vsa_rotateleft_simplifier(a, b):
    # TODO
    return None


def vsa_rotateright_simplifier(a, b):
    # TODO
    return None


def vsa_lshiftr_simplifier(a, b):
    # TODO
    return None


def vsa_ugt_simplifier(a, b):
    # TODO
    return None


def vsa_uge_simplifier(a, b):
    # TODO
    return None


def vsa_ult_simplifier(a, b):
    # TODO
    return None


def vsa_ule_simplifier(a, b):
    # TODO
    return None


def vsa_sgt_simplifier(a, b):
    # TODO
    return None


def vsa_sge_simplifier(a, b):
    # TODO
    return None


def vsa_slt_simplifier(a, b):
    # TODO
    return None


def vsa_sle_simplifier(a, b):
    # TODO
    return None


def vsa_concat_simplifier(a, b):
    # TODO
    return None


def vsa_extract_simplifier(high, low, base):
    # TODO
    return None


def vsa_zeroext_simplifier(base, amount):
    # TODO
    return None


def vsa_signext_simplifier(base, amount):
    # TODO
    return None


def vsa_if_simplifier(cond, then, els):
    # TODO
    return None


def vsa_reverse_simplifier(a):
    # TODO
    return None


vsa_simplifications = {
    "BVSetUnion": vsa_union_simplifier,
    "BVSetIntersection": vsa_intersection_simplifier,
    "BVSetWiden": vsa_widen_simplifier,
    "BVSetAdd": vsa_add_simplifier,
    "BVSetSub": vsa_sub_simplifier,
    "BVSetMul": vsa_mul_simplifier,
    "BVSetMod": vsa_mod_simplifier,
    "BVSetAnd": vsa_and_simplifier,
    "BVSetOr": vsa_or_simplifier,
    "BVSetXor": vsa_xor_simplifier,
    "BVSRotateLeft": vsa_rotateleft_simplifier,
    "BVSRotateRight": vsa_rotateright_simplifier,
    "BVSLShiftr": vsa_lshiftr_simplifier,
    "BVSetUGT": vsa_ugt_simplifier,
    "BVSetUGE": vsa_uge_simplifier,
    "BVSetULT": vsa_ult_simplifier,
    "BVSetULE": vsa_ule_simplifier,
    "BVSetSGT": vsa_sgt_simplifier,
    "BVSetSGE": vsa_sge_simplifier,
    "BVSetSLT": vsa_slt_simplifier,
    "BVSetSLE": vsa_sle_simplifier,
    "BVSetConcat": vsa_concat_simplifier,
    "BVSetExtract": vsa_extract_simplifier,
    "BVSetZeroExt": vsa_zeroext_simplifier,
    "BVSetSignExt": vsa_signext_simplifier,
    "If": vsa_if_simplifier,
    "Reverse": vsa_reverse_simplifier,
}
