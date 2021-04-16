/**
 * @file
 * @brief This file contains the possible Expression exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __ERROR_EXPRESSION_HPP__
#define __ERROR_EXPRESSION_HPP__

#include "../utils.hpp"


namespace Error::Expression {

    /** Claripy Expression exception */
    using Claripy = Utils::Error::Python::Claripy;

    // Intermediate classes

    /** Expression Balance exception */
    DEFINE_NONFINAL_EXCEPTION(Balancer, Claripy);
    /** Expression Operation exception */
    DEFINE_NONFINAL_EXCEPTION(Operation, Claripy);

    // Final classes

    /** @todo document */
    DEFINE_FINAL_EXCEPTION(BalancerUnsat, Balancer);
    /** @todo document */
    DEFINE_FINAL_EXCEPTION(Type, Claripy);
    /** @todo document */
    DEFINE_FINAL_EXCEPTION(Value, Claripy);
    /** @todo document */
    DEFINE_FINAL_EXCEPTION(Size, Claripy);
    /** @todo document */
    DEFINE_FINAL_EXCEPTION(Replacement, Claripy);
    /** @todo document */
    DEFINE_FINAL_EXCEPTION(Recursion, Operation);
    /** @todo document */
    DEFINE_FINAL_EXCEPTION(ZeroDivision, Operation);

} // namespace Error::Expression

#endif
