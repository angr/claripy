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


namespace Error {

    // Expression errors
    namespace Expression {

        /** Claripy Expression exception */
        using Claripy = Utils::Error::Python::Claripy;

        // Intermediate classes

        /** Expression Balance exception */
        DEFINE_NONFINAL_INSTANTIABLE_SUBCLASS_WITH_CTOR(Balancer, Claripy)
        /** Expression Operation exception */
        DEFINE_NONFINAL_INSTANTIABLE_SUBCLASS_WITH_CTOR(Operation, Claripy)

        // Final classes

        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(BalancerUnsat, Balancer)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Type, Claripy)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Value, Claripy)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Size, Claripy)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Replacement, Claripy)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Recursion, Operation)
        /** @todo document */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(ZeroDivision, Operation)

    } // namespace Expression

} // namespace Error

#endif
