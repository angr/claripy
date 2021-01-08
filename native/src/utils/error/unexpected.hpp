/**
 * @file
 * \ingroup utils
 * @brief This file contains the possible exceptions that indicate an internal claricpp failur
 * These exceptions are not expected to be raised if claricpp is operating as intended
 */
#ifndef __ERRORS_UNEXPECTED_HPP__
#define __ERRORS_UNEXPECTED_HPP__

#include "claricpp.hpp"


namespace Utils::Error {

    // Errors that indicate a code issue
    // These should never be thrown unless a claricpp bug occurs
    namespace Unexpected {

        /** Base unexpected exception
         *  All unexpected exceptions must derive from this
         */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Base, Claricpp)

        /** Bad cast exception */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(BadCast, Base)

        /** Raised when a function is given invalid arguments */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(IncorrectUsage, Claricpp)

        /** Raised when something that should never be possible occurs */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Illegal, Claricpp)

    } // namespace Unexpected

} // namespace Utils::Error

#endif
