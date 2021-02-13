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

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The op class: Neg */
    OP_UNARY_TRIVIAL_SUBCLASS(Neg)

    /** The op class: Abs */
    OP_UNARY_TRIVIAL_SUBCLASS(Abs)

    /** The op class: Invert */
    OP_UNARY_TRIVIAL_SUBCLASS(Invert)

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    /** The comparison op class: Eq */
    OP_BINARY_TRIVIAL_SUBCLASS(Eq, true)

    /** The comparison op class: Sub */
    OP_BINARY_TRIVIAL_SUBCLASS(Sub, true)

    /** The comparison op class: Concat */
    OP_BINARY_TRIVIAL_SUBCLASS(Concat, false)

} // namespace Op

#endif
