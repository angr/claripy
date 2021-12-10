/**
 * @file
 * @brief This file contains the possible Expr exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 */
#ifndef R_ERROR_EXPR_HPP_
#define R_ERROR_EXPR_HPP_

#include "../util.hpp"


namespace Error::Expr {

    /** Claripy Expr exception */
    using Claripy = Util::Err::Python::Claripy;

    // Intermediate classes

    /** Expr Balance exception */
    //    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Balancer, Claripy);
    /** Expr Operation exception */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Operation, Claripy);

    // Final classes

    /** Expr usage exception */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Usage, Claripy);
    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Type, Claripy);
    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Value, Claripy);
    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Size, Claripy);
    /** @todo document */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(ZeroDivision, Operation);

} // namespace Error::Expr

#endif
