/**
 * @file
 * @brief Define trivial fp subclass ops
 */
#ifndef __OP_FP_TRIVIAL_HPP__
#define __OP_FP_TRIVIAL_HPP__

#include "mode_binary.hpp"

#include "../ternary.hpp"


namespace Op::FP {

    /**********************************************************/
    /*               FP Mode Binary Subclasses                */
    /**********************************************************/

    /** The op class: FP::Add */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Add);

    /** The op class: FP::Sub */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Sub);

    /** The op class: FP::Div */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Div);

    /**********************************************************/
    /*                   Ternary Subclasses                   */
    /**********************************************************/

    /** The ternary op class: FP
     *  Input sizes may differ
     */
    OP_TERNARY_TRIVIAL_SUBCLASS(FP, false);

} // namespace Op::FP

#endif
