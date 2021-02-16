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
    /*                    Flat Subclasses                     */
    /**********************************************************/

    /** The op class: Add */
    OP_FLAT_TRIVIAL_SUBCLASS(Add, true)

    /** The op class: Mul */
    OP_FLAT_TRIVIAL_SUBCLASS(Mul, true)

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The op class: Neg */
    OP_UNARY_TRIVIAL_SUBCLASS(Neg)

    /** The op class: Abs */
    OP_UNARY_TRIVIAL_SUBCLASS(Abs)

    /** The op class: Invert */
    OP_UNARY_TRIVIAL_SUBCLASS(Invert)

    /** The op class: Reverse */
    OP_UNARY_TRIVIAL_SUBCLASS(Reverse)

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    /** The comparison op class: Eq */
    OP_BINARY_TRIVIAL_SUBCLASS(Eq, true)

    /** The comparison op class: Sub */
    OP_BINARY_TRIVIAL_SUBCLASS(Sub, true)

    /** The comparison op class: Div */
    OP_BINARY_TRIVIAL_SUBCLASS(Div, true)

    /** The comparison op class: Concat */
    OP_BINARY_TRIVIAL_SUBCLASS(Concat, false)

    /** The comparison op class: Or */
    OP_BINARY_TRIVIAL_SUBCLASS(Or, true)

    /** The comparison op class: And */
    OP_BINARY_TRIVIAL_SUBCLASS(And, true)

    /** The comparison op class: Xor */
    OP_BINARY_TRIVIAL_SUBCLASS(Xor, true)

    /** The comparison op class: Pow */
    OP_BINARY_TRIVIAL_SUBCLASS(Pow, true)

    /** The comparison op class: Mod */
    OP_BINARY_TRIVIAL_SUBCLASS(Mod, true)

    /** The comparison op class: DivMod */
    OP_BINARY_TRIVIAL_SUBCLASS(DivMod, true)

} // namespace Op

#endif
