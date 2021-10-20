/**
 * @file
 * @brief This file contains the possible Expr exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef R_ERROR_EXPR_HPP_
#define R_ERROR_EXPR_HPP_

#include "../util.hpp"


namespace Error::Expr {

    /** Claripy Expr exception */
    using Claripy = Util::Err::Python::Claripy;

    // Intermediate classes

    /** Expr Balance exception */
    DEFINE_NONFINAL_EXCEPTION(Balancer, Claripy);
    /** Expr Operation exception */
    DEFINE_NONFINAL_EXCEPTION(Operation, Claripy);

    // Final classes

    /** Expr usage exception */
    DEFINE_NONFINAL_EXCEPTION(Usage, Claripy);
    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(BalancerUnsat, Balancer);
    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Type, Claripy);
    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Value, Claripy);
    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Size, Claripy);
    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Replacement, Claripy);
    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Recursion, Operation);
    /** @todo document */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(ZeroDivision, Operation);

} // namespace Error::Expr

#endif
