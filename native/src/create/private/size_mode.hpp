/**
 * @file
 * @brief This file defines modes for how Expr sizes are computed
 */
#ifndef R_SRC_CREATE_PRIVATE_SIZEMODE_HPP_
#define R_SRC_CREATE_PRIVATE_SIZEMODE_HPP_

#include "../../expr.hpp"


namespace Create::Private {

    /** Modes that determine how Expr sizes are computed */
    enum class SizeMode {
        /** Not Applicable */
        NA,
        /** First operand's size is selected */
        First,
        /** Second operand's size is selected */
        Second,
        /** All operand sizes are summed */
        Add
    };

} // namespace Create::Private

#endif
