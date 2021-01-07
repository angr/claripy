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
        DEFINE_NAMESPACED_SUBCLASS_WITH_CONSTRUCTOR(Base, Claricpp, Utils::Error)

        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Balancer, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(BalancerUnsat, Balancer)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Type, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Value, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Size, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Operation, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Replacement, Base)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Recursion, Operation)
        /** @todo document */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(ZeroDivision, Operation)

    } // namespace Expression

} // namespace Error

#endif
