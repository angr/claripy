/**
 * @file
 * @brief Define trivial subclass ops
 */
#ifndef __OP_TRIVIAL_HPP__
#define __OP_TRIVIAL_HPP__

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

    /** The unary op class: Neg */
    OP_UNARY_TRIVIAL_SUBCLASS(Neg, 0);

    /** The unary mathematical op class: Abs */
    OP_UNARY_TRIVIAL_SUBCLASS(Abs, 0);

    /** The unary op class: Invert */
    OP_UNARY_TRIVIAL_SUBCLASS(Invert, 0);

    /** The unary bitwise op class: Reverse */
    OP_UNARY_TRIVIAL_SUBCLASS(Reverse, 0);

    /**********************************************************/
    /*                  UIntBinary Subclasses                 */
    /**********************************************************/

    /** The int binary op class: SignExt */
    OP_UINTBINARY_TRIVIAL_SUBCLASS(SignExt, 0);

    /** The int binary op class: ZeroExt */
    OP_UINTBINARY_TRIVIAL_SUBCLASS(ZeroExt, 0);

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    // Comparisons

    /** The binary comparison op class: Eq
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Eq, true, 0);

    /** The binary comparison op class: Neq */
    OP_BINARY_TRIVIAL_SUBCLASS(Neq, false, 0);

    /** The binary comparison op class(es): ULT, SLT, UGT, SGT, ULE, SLE, UGE, SGE
     *  Requires equal sized inputs
     */
    template <Mode::Compare Mask>
    OP_BINARY_TRIVIAL_SUBCLASS(Compare, true,
                               static_cast<std::underlying_type_t<Mode::Shift>>(Mask));

    // Math

    /** The mathematical binary op class: Sub
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Sub, true, 0);

    /** The mathematical binary op class: Div
     *  Requires equal sized inputs
     */
    template <bool Signed> OP_BINARY_TRIVIAL_SUBCLASS(Div, true, static_cast<int>(Signed));

    /** The mathematical binary op class: Pow
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Pow, true, 0);

    /** The mathematical binary op class: Mod
     *  Requires equal sized inputs
     */
    template <bool Signed> OP_BINARY_TRIVIAL_SUBCLASS(Mod, true, static_cast<int>(Signed));

    // Bitwise

    /** The bitwise binary op class: Shift
     *  Requires equal sized inputs
     */
    template <Mode::Shift Mask>
    OP_BINARY_TRIVIAL_SUBCLASS(Shift, true,
                               static_cast<std::underlying_type_t<Mode::Shift>>(Mask));

    /** The bitwise binary op class: Rotate
     *  Requires equal sized inputs
     */
    template <bool Left> OP_BINARY_TRIVIAL_SUBCLASS(Rotate, true, static_cast<int>(Left));

    // Misc

    /** The set binary op class: Widen
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Widen, true, 0);

    /** The set binary op class: Union
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Union, true, 0);

    /** The set binary op class: Inersection
     *  Requires equal sized inputs
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Intersection, true, 0);

    /** The binary op class: Concat
     *  Input sizes may differ
     */
    OP_BINARY_TRIVIAL_SUBCLASS(Concat, false, 0);

    /**********************************************************/
    /*                    Flat Subclasses                     */
    /**********************************************************/

    // Math

    /** The flat math op class: Add
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Add, true, 0);

    /** The flat op class: Mul
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Mul, true, 0);

    // Logical

    /** The flat op class: Or
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Or, true, 0);

    /** The flat op class: And
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(And, true, 0);

    /** The flat op class: Xor
     *  Requires equal sized inputs
     */
    OP_FLAT_TRIVIAL_SUBCLASS(Xor, true, 0);

} // namespace Op

#endif
