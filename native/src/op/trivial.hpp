/**
 * @file
 * @brief Define trivial subclass ops
 */
#ifndef __OP_TRIVIAL_HPP__
#define __OP_TRIVIAL_HPP__

#include "binary.hpp"
#include "flat.hpp"
#include "int_binary.hpp"
#include "unary.hpp"


namespace Op {

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The unary op class: Neg */
    OP_UNARY_TRIVIAL_SUBCLASS(Neg);

    /** The unary mathematical op class: Abs */
    OP_UNARY_TRIVIAL_SUBCLASS(Abs);

    /** The unary op class: Invert */
    OP_UNARY_TRIVIAL_SUBCLASS(Invert);

    /** The unary bitwise op class: Reverse */
    OP_UNARY_TRIVIAL_SUBCLASS(Reverse);

    /**********************************************************/
    /*                  IntBinary Subclasses                  */
    /**********************************************************/

    /** The int binary op class: SignExt */
    OP_INTBINARY_TRIVIAL_SUBCLASS(SignExt, true);

    /** The int binary op class: ZeroExt */
    OP_INTBINARY_TRIVIAL_SUBCLASS(ZeroExt, true);

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    // Comparisons

    /** The binary comparison op class: Eq
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Eq, true);

    /** The binary comparison op class(es): ULT, SLT, UGT, SGT, ULE, SLE, UGE, SGE
     *  Requires equal sized inputs
     */
    template <bool Signed, bool Less, bool Eq> OP_BINARY_TRIVIAL_SUBCLASS(Compare, true);

    // Math

    /** The mathematical binary op class: Sub
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Sub, true);

    /** The mathematical binary op class: Div
     *  Requires equal sized inputs
     */
    template <bool Signed> OP_BINARY_TRIVIAL_SUBCLASS(Div, true);

    /** The mathematical binary op class: Pow
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Pow, true);

    /** The mathematical binary op class: Mod
     *  Requires equal sized inputs
     */
    template <bool Signed> OP_BINARY_TRIVIAL_SUBCLASS(Mod, true);

    // Bitwise

    /** The bitwise binary op class: Shift
     *  Requires equal sized inputs
     */
    template <bool Arithmetic, bool Left> OP_BINARY_TRIVIAL_SUBCLASS(Shift, true);

    /** The bitwise binary op class: Rotate
     *  Requires equal sized inputs
     */
    template <bool Left> OP_BINARY_TRIVIAL_SUBCLASS(Rotate, true);

    // Misc

    /** The set binary op class: Widen
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Widen, true);

    /** The set binary op class: Union
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Union, true);

    /** The set binary op class: Inersection
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Intersection, true);

    /** The binary op class: Concat
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Concat, false);

    /**********************************************************/
    /*                    Flat Subclasses                     */
    /**********************************************************/

    // Math

    /** The flat math op class: Add
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Add, true);

    /** The flat op class: Mul
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Mul, true);

    // Logical

    /** The flat op class: Or
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Or, true);

    /** The flat op class: And
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(And, true);

    /** The flat op class: Xor
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Xor, true);

} // namespace Op

#endif
