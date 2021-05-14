/**
 * @file
 * @brief This file defines modes for how Expression sizes are computed
 */
#ifndef R_CREATE_PRIVATE_SIZEMODE_HPP_
#define R_CREATE_PRIVATE_SIZEMODE_HPP_

#include "../../expression.hpp"


namespace Create::Private {

    /** Modes that determine how Expression sizes are computed */
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

    /** A shortcut for selecting First if T is a subclass of Bits, else NA */
    template <typename T>
    inline const constexpr SizeMode first_or_na {
        Utils::select<Utils::is_ancestor<Expression::Bits, T>, SizeMode::First, SizeMode::NA>
    };

} // namespace Create::Private

#endif
