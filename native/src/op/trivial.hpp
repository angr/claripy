/**
 * @file
 * @brief Define trivial subclass ops
 */
#ifndef __OP_TRIVIAL_HPP__
#define __OP_TRIVIAL_HPP__

#include "binary.hpp"
#include "flat.hpp"


// Forward declarations
namespace Expression {
    class Bits;
}

namespace Op {

    /**********************************************************/
    /*                    Flat Subclasses                     */
    /**********************************************************/

    /** The op class: Add */
    OP_FLAT_TRIVIAL_SUBCLASS(Add)

    /**********************************************************/
    /*                   Binary Subclasses                    */
    /**********************************************************/

    /** The comparison op class: Eq */
    OP_BINARY_TRIVIAL_SUBCLASS(Eq)

    /** The comparison op class: Concat */
    OP_BINARY_TRIVIAL_SUBCLASS(Concat, Expression::Bits)

} // namespace Op

#endif
