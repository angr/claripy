/**
 * @file
 * @brief Define trivial fp subclass ops
 */
#ifndef R_SRC_OP_FP_TRIVIAL_HPP_
#define R_SRC_OP_FP_TRIVIAL_HPP_

#include "mode_binary.hpp"

#include "../binary.hpp"
#include "../ternary.hpp"
#include "../unary.hpp"


namespace Op::FP {

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The unary fp op class: FP::IsNan */
    OP_UNARY_TRIVIAL_SUBCLASS(IsNan, "FP::");

    /** The unary fp op class: FP::ToIEEEBV */
    OP_UNARY_TRIVIAL_SUBCLASS(ToIEEEBV, "FP::");

    /**********************************************************/
    /*               FP Mode Binary Subclasses                */
    /**********************************************************/

    /** The op class: FP::Add
     *  Input sizes may not differ
     */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Add, "FP::");

    /** The op class: FP::Sub
     *  Input sizes may not differ
     */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Sub, "FP::");

    /** The op class: FP::Mul
     *  Input sizes may not differ
     */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Mul, "FP::");

    /** The op class: FP::Div
     *  Input sizes may not differ
     */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Div, "FP::");

    /**********************************************************/
    /*                   Ternary Subclasses                   */
    /**********************************************************/

    /** The ternary op class: FP::FP
     *  Input sizes may differ
     */
    OP_TERNARY_TRIVIAL_SUBCLASS(FP, false, "FP::");

} // namespace Op::FP

#endif
