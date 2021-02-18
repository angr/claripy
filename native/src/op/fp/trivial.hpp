/**
 * @file
 * @brief Define trivial fp subclass ops
 */
#ifndef __OP_FP_TRIVIAL_HPP__
#define __OP_FP_TRIVIAL_HPP__

#include "mode_binary.hpp"

#include "../binary.hpp"
#include "../ternary.hpp"
#include "../unary.hpp"


namespace Op::FP {

    /**********************************************************/
    /*                    Unary Subclasses                    */
    /**********************************************************/

    /** The unary fp op class: FP::ToIEEEBV */
    OP_UNARY_TRIVIAL_SUBCLASS(ToIEEEBV);

    /** The unary fp op class: FP::IsInf */
    OP_UNARY_TRIVIAL_SUBCLASS(IsInf);

    /** The unary fp op class: FP::IsNaN */
    OP_UNARY_TRIVIAL_SUBCLASS(IsNaN);

    /**********************************************************/
    /*               FP Mode Binary Subclasses                */
    /**********************************************************/

    /** The op class: FP::NE
     *  Input sizes must be the same
     */
    OP_BINARY_TRIVIAL_SUBCLASS(NE, true);

    /**********************************************************/
    /*               FP Mode Binary Subclasses                */
    /**********************************************************/

    /** The op class: FP::Add
     *  Input sizes may not differ
     */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Add);

    /** The op class: FP::Sub
     *  Input sizes may not differ
     */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Sub);

    /** The op class: FP::Div
     *  Input sizes may not differ
     */
    OP_FP_MODEBINARY_TRIVIAL_SUBCLASS(Div);

    /**********************************************************/
    /*                   Ternary Subclasses                   */
    /**********************************************************/

    /** The ternary op class: FP::FP
     *  Input sizes may differ
     */
    OP_TERNARY_TRIVIAL_SUBCLASS(FP, false);

} // namespace Op::FP

#endif
