/**
 * @file
 * @brief This file contains the possible AST exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __ERRORS_AST_HPP__
#define __ERRORS_AST_HPP__

#include "claricpp.hpp"
#include "factory.hpp"


/** A namespace used for the errors directory */
namespace Errors {

    /** A namespace used for AST errors */
    namespace AST {

        /** Base AST exception
         *  All AST exceptions must derive from this
         */
        class Base : public Claricpp {};

        /** @todo document */
        class Balancer : public Base {};
        /** @todo document */
        class BalancerUnsat : public Balancer {};
        /** @todo document */
        class Type : public Base {};
        /** @todo document */
        class Value : public Base {};
        /** @todo document */
        class Size : public Base {};
        /** @todo document */
        class Operation : public Base {};
        /** @todo document */
        class Replacement : public Base {};
        /** @todo document */
        class Recursion : public Operation {};
        /** @todo document */
        class ZeroDivision : public Operation {};

    } // namespace AST

} // namespace Errors

#endif
