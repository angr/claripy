/**
 * @file
 * @brief This file contains the possible Expr exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 */
#ifndef R_SRC_ERROR_EXPR_HPP_
#define R_SRC_ERROR_EXPR_HPP_

#include "../util.hpp"


namespace Error::Expr {

    /** Claripy Expr exception */
    using Claripy = Util::Err::Python::Claripy;

    /** Expr Operation exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Operation, Claripy);
    /** Expr usage exception */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Usage, Claripy);
    /** Expr type exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Type, Claripy);
    /** Expr value exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Value, Claripy);
    /** Expr size exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Size, Claripy);

} // namespace Error::Expr

#endif
