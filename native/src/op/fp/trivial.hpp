/**
 * @file
 * @brief Define trivial subclass ops
 */
#ifndef __OP_FP_TRIVIAL_HPP__
#define __OP_FP_TRIVIAL_HPP__

#include "mode_binary.hpp"


namespace Op {

    /**********************************************************/
    /*               FP Mode Binary Subclasses                */
    /**********************************************************/

    namespace FP {

        /** The op class: FP::Add */
        OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Add)

    } // namespace FP

} // namespace Op

#endif
