/**
 * @file
 * @brief This file defines constants used across Create
 */
#ifndef R_CREATE_CONSTANTS_HPP_
#define R_CREATE_CONSTANTS_HPP_

#include "../expr.hpp"


// For files that include this
#include "../error.hpp"
#include "../op.hpp"
#include "../simplification.hpp"


namespace Create {

    /** A shortcut for Ptr<Expr::Base> */
    using EBasePtr = Expr::BasePtr;

} // namespace Create

#endif
