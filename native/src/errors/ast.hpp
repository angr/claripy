/**
 * @file
 * @brief This file contains the possible AST exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __ERRORS_AST_HPP__
#define __ERRORS_AST_HPP__

#include "../utils.hpp"


namespace Errors {

    // AST errors
    namespace AST {

        /** Base AST exception
         *  All AST exceptions must derive from this
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

    } // namespace AST

} // namespace Errors

#endif
