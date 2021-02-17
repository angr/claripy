/**
 * @file
 * @brief Define trivial subclass ops
 */
#ifndef __OP_TRIVIAL_HPP__
#define __OP_TRIVIAL_HPP__

#include "binary.hpp"
#include "flat.hpp"
#include "unary.hpp"


// Forward declarations
namespace Expression {
    class Bits;
    class BV;
} // namespace Expression

namespace Op {

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The op class: Neg */
    OP_UNARY_TRIVIAL_SUBCLASS(Neg);

    /** The op class: Abs */
    OP_UNARY_TRIVIAL_SUBCLASS(Abs);

    /** The op class: Invert */
    OP_UNARY_TRIVIAL_SUBCLASS(Invert);

    /** The op class: Reverse */
    OP_UNARY_TRIVIAL_SUBCLASS(Reverse);

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    // Comparisons

    /** The comparison op class: Eq */
    OP_BINARY_TRIVIAL_SUBCLASS(Eq, true);

    /** The comparison op class(es): ULT, SLT, UGT, SGT, ULE, SLE, UGE, SGE */
    template <bool Signed, bool Less, bool Eq> OP_BINARY_TRIVIAL_SUBCLASS(Compare, true);

    // Math

    /** The op class: Sub */
    OP_BINARY_TRIVIAL_SUBCLASS(Sub, true);

    /** The op class: Div */
    OP_BINARY_TRIVIAL_SUBCLASS(Div, true);

    /** The op class: Pow */
    OP_BINARY_TRIVIAL_SUBCLASS(Pow, true);

    /** The op class: Mod */
    OP_BINARY_TRIVIAL_SUBCLASS(Mod, true);

    /** The op class: DivMod */
    OP_BINARY_TRIVIAL_SUBCLASS(DivMod, true);

    // Bitwise

    /** The op class: LogicalShift */
    template <bool Left> OP_BINARY_TRIVIAL_SUBCLASS(LogicalShift, true);

    /** The op class: ArithmeticShift */
    template <bool Left> OP_BINARY_TRIVIAL_SUBCLASS(ArithmeticShift, true);

    /** The op class: Rotate */
    template <bool Left> OP_BINARY_TRIVIAL_SUBCLASS(Rotate, true);

    // Misc

    /** The op class: Widen */
    OP_BINARY_TRIVIAL_SUBCLASS(Widen, true);

    /** The op class: Union */
    OP_BINARY_TRIVIAL_SUBCLASS(Union, true);

    /** The op class: Inersection */
    OP_BINARY_TRIVIAL_SUBCLASS(Intersection, true);

    /** The op class: Concat */
    OP_BINARY_TRIVIAL_SUBCLASS(Concat, false);

    /**********************************************************/
    /*                    Flat Subclasses                     */
    /**********************************************************/

    // Math

    /** The op class: Add */
    OP_FLAT_TRIVIAL_SUBCLASS(Add, true);

    /** The op class: Mul */
    OP_FLAT_TRIVIAL_SUBCLASS(Mul, true);

    // Logical
    /** The op class: Or */
    OP_FLAT_TRIVIAL_SUBCLASS(Or, true);

    /** The op class: And */
    OP_FLAT_TRIVIAL_SUBCLASS(And, true);

    /** The op class: Xor */
    OP_FLAT_TRIVIAL_SUBCLASS(Xor, true);

} // namespace Op

#endif
