from __future__ import annotations

backend_comparator_operations = {
    "SGE",
    "SLE",
    "SGT",
    "SLT",
    "UGE",
    "ULE",
    "UGT",
    "ULT",
}

backend_bitwise_operations = {
    "RotateLeft",
    "RotateRight",
    "LShR",
    "Reverse",
}

backend_boolean_operations = {"And", "Or", "Not"}

backend_bitmod_operations = {"Concat", "Extract", "SignExt", "ZeroExt"}

backend_creation_operations = {"BoolV", "BVV", "FPV", "StringV"}

backend_symbol_creation_operations = {"BoolS", "BVS", "FPS", "StringS"}

backend_other_operations = {"If"}

backend_arithmetic_operations = {"SDiv", "SMod"}

backend_operations = (
    backend_comparator_operations
    | backend_bitwise_operations
    | backend_boolean_operations
    | backend_bitmod_operations
    | backend_creation_operations
    | backend_other_operations
    | backend_arithmetic_operations
)
backend_operations_vsa_compliant = (
    backend_bitwise_operations | backend_comparator_operations | backend_boolean_operations | backend_bitmod_operations
)

backend_fp_cmp_operations = {
    "fpLT",
    "fpLEQ",
    "fpGT",
    "fpGEQ",
    "fpEQ",
}

backend_fp_operations = {
    "FPS",
    "fpToFP",
    "fpToFPUnsigned",
    "fpToIEEEBV",
    "fpFP",
    "fpToSBV",
    "fpToUBV",
    "fpNeg",
    "fpSub",
    "fpAdd",
    "fpMul",
    "fpDiv",
    "fpAbs",
    "fpIsNaN",
    "fpIsInf",
    "fpSqrt",
} | backend_fp_cmp_operations

backend_strings_operations = {
    "StrSubstr",
    "StrReplace",
    "StrConcat",
    "StrLen",
    "StrContains",
    "StrPrefixOf",
    "StrSuffixOf",
    "StrIndexOf",
    "StrToInt",
    "StrIsDigit",
    "IntToStr",
}

expression_set_operations = {
    # Set operations
    "union",
    "intersection",
    "widen",
}

bound_ops = {
    "Not": "__invert__",
    "And": "__and__",
    "Or": "__or__",
}
