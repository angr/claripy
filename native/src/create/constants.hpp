/**
 * @file
 * @brief This file defines constants used across Create
 */
#ifndef __CREATE_CONSTANTS_HPP__
#define __CREATE_CONSTANTS_HPP__

#include "../expression.hpp"


// For files that include this
#include "../error.hpp"
#include "../op.hpp"
#include "../simplification.hpp"


namespace Create {

    /** A shortcut for an annotation vector */
    using EAnVec = Expression::Base::AnVec;

    /** A shortcut for a factory pointer */
    template <typename T> using Ptr = Factory::Ptr<T>;

    /** A shortcut for Ptr<Expression::Base> */
    using EBasePtr = Ptr<Expression::Base>;

    /** An abbreviation for Constants::CTSC */
    template <typename T> using CTSC = Constants::CTSC<T>;

} // namespace Create

#endif
