/**
 * @file
 * @brief This file contains the possible Expression exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef R_ERROR_EXPRESSION_HPP_
#define R_ERROR_EXPRESSION_HPP_

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

} // namespace Error::Expression

#endif
