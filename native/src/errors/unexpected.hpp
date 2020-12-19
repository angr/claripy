/**
 * @file
 * @brief This file contains the possible exceptions that indicate an internal claricpp failur
 * These exceptions are not expected to be raised if claricpp is operating as intended
 */
#ifndef __ERRORS_UNEXPECTED_HPP__
#define __ERRORS_UNEXPECTED_HPP__

#include "claricpp.hpp"

#include "../macros.hpp"


/** A namespace used for the errors directory */
namespace Errors {

    /** A namespace used for unexpected errors */
    namespace Unexpected {

        /** Base unexpected exception
         *  All unexpected exceptions must derive from this
         */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Base, Claricpp)

        /** Bad cast exception */
        struct BadCast : public Base, virtual public std::bad_cast {
            /** Inherit constructors */
            using Base::Base;
        };

        /** Raised when a function is given invalid arguments */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(IncorrectUsage, Claricpp)

    } // namespace Unexpected

} // namespace Errors

#endif
