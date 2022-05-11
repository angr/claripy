/**
 * @file
 * @brief Define trivial subclass ops
 */
#ifndef R_SRC_OP_TRIVIAL_HPP_
#define R_SRC_OP_TRIVIAL_HPP_

#include "binary.hpp"
#include "flat.hpp"
#include "uint_binary.hpp"
#include "unary.hpp"

#include "../mode.hpp"

#include <type_traits>


namespace Op {

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The unary mathematical op class: Abs */
    OP_UNARY_TRIVIAL_SUBCLASS(Abs, "");

    /** The unary op class: Neg */
    OP_UNARY_TRIVIAL_SUBCLASS(Neg, "");

    /** The unary op class: Not */
    OP_UNARY_TRIVIAL_SUBCLASS(Not, "");

    /** The unary op class: Invert */
    OP_UNARY_TRIVIAL_SUBCLASS(Invert, "");

    /** The unary bitwise op class: Reverse */
    OP_UNARY_TRIVIAL_SUBCLASS(Reverse, "");

    /**********************************************************/
    /*                  UIntBinary Subclasses                 */
    /**********************************************************/

    /** The int binary op class: SignExt */
    OP_UINTBINARY_TRIVIAL_SUBCLASS(SignExt, "");

    /** The int binary op class: ZeroExt */
    OP_UINTBINARY_TRIVIAL_SUBCLASS(ZeroExt, "");

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    // Comparisons

    /** The binary comparison op class: Eq
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(Eq, Binary<true>, "");

    /** The binary comparison op class: Neq */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(Neq, Binary<false>, "");

    /** The binary comparison op class: Inequality */
    OP_BINARY_TRIVIAL_PURE_SUBCLASS(Inequality, true);
    /** Unsigned >= comparison op */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(UGE, Inequality, "");
    /** Unsigned > comparison op */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(UGT, Inequality, "");
    /** Unsigned <= comparison op */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(ULE, Inequality, "");
    /** Unsigned < comparison op */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(ULT, Inequality, "");
    /** Signed >= comparison op */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(SGE, Inequality, "");
    /** Signed > comparison op */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(SGT, Inequality, "");
    /** Signed <= comparison op */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(SLE, Inequality, "");
    /** Signed < comparison op */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(SLT, Inequality, "");

    // Math

    /** The mathematical binary op class: Sub
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(Sub, Binary<true>, "");

    /** The mathematical binary op: Div
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_PURE_SUBCLASS(Div, true);
    /** The signed div op class */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(DivSigned, Div, "");
    /** The unsigned div op class */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(DivUnsigned, Div, "");

    /** The mathematical binary op: Mod
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_PURE_SUBCLASS(Mod, true);
    /** The signed mod op class */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(ModSigned, Div, "");
    /** The unsigned mod op class */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(ModUnsigned, Div, "");

    // Bitwise

    /** The bitwise binary op class: Shift
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_PURE_SUBCLASS(Shift, true);
    /** The bitwise left shift op class */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(ShiftLeft, Shift, "");
    /** The bitwise logical right shift op class */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(ShiftLogicalRight, Shift, "");
    /** The bitwise arithmetic right shift op class */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(ShiftArithmeticRight, Shift, "");

    /** Abstract bitwise binary rotations
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_PURE_SUBCLASS(Rotate, true);
    /** The bitwise binary op class: RotateLeft */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(RotateLeft, Rotate, "");
    /** The bitwise binary op class: RotateRight */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(RotateRight, Rotate, "");

    // Misc

    /** The set binary op class: Widen
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(Widen, Binary<true>, "");

    /** The set binary op class: Union
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(Union, Binary<true>, "");

    /** The set binary op class: Intersection
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_FINAL_DESCENDANT(Intersection, Binary<true>, "");

    /**********************************************************/
    /*                    Flat Subclasses                     */
    /**********************************************************/

    /** The flat op class: Concat
     *  Input sizes may differ
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Concat, false, "");

    // Math

    /** The flat math op class: Add
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Add, true, "");

    /** The flat op class: Mul
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Mul, true, "");

    // Logical

    /** The flat op class: Or
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Or, true, "");

    /** The flat op class: And
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(And, true, "");

    /** The flat op class: Xor
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Xor, true, "");

} // namespace Op

#endif
