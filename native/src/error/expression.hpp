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

        /** Base Expression exception
         *  All Expression exceptions must derive from this
         */
        DEFINE_NAMESPACED_SUBCLASS_WITH_CTOR(Base, Claripy, Utils::Error::Python)

        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(Balancer, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(BalancerUnsat, Balancer)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(Type, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(Value, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(Size, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(Operation, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(Replacement, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(Recursion, Operation)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CTOR(ZeroDivision, Operation)

    } // namespace Expression

} // namespace Error

#endif
