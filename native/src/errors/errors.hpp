/**
 * @file
 * @brief This file contains the possible exceptions claricpp can raise
 * These exceptions have python analogs and must be caught and set to python
 * via a different method.
 * @todo Document method when known
 */
#ifndef __ERRORS_ERRORS_HPP__
#define __ERRORS_ERRORS_HPP__

#include <exception>
#include <string>


/** A namespace used for the errors directory */
namespace Errors {

    /** Base AST exception
     *  All AST exceptions must derive from this
     */
    class AST : public std::exception {
      public:
        /** Constructor */
        AST(const char *const what);

        /** Message getter */
        const char *what() const throw();

      private:
        /** The message */
        const std::string msg;
    };

    /** @todo document */
    class Balancer : public AST {};
    /** @todo document */
    class BalancerUnsat : public Balancer {};
    /** @todo document */
    class Type : public AST {};
    /** @todo document */
    class Value : public AST {};
    /** @todo document */
    class Size : public AST {};
    /** @todo document */
    class Operation : public AST {};
    /** @todo document */
    class Replacement : public AST {};
    /** @todo document */
    class Recursion : public Operation {};
    /** @todo document */
    class ZeroDivision : public Operation {};

} // namespace Errors

#endif
