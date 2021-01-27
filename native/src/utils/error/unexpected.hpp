/**
 * @file
 * \ingroup utils
 * @brief This file contains the possible exceptions that indicate an internal claricpp failur
 * These exceptions are not expected to be raised if claricpp is operating as intended
 * Note: these exceptions ignore the rule of 5 (see claricpp.hpp)
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
        struct Base : public Claricpp {

            /** Inherit constructors */
            using Claricpp::Claricpp;

            /** Virtual destructor */
            virtual ~Base() noexcept;
        };

        /** Bad cast exception */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(BadCast, Base)

        /** Raised when a function is given invalid arguments */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(IncorrectUsage, Claricpp)

        /** Raised when a recurrence gaurded function recurrses too many times */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(RecurrenceLimit, Claricpp)

        /** Raised when something unknown occurs */
        DEFINE_SUBCLASS_WITH_CONSTRUCTOR(Unknown, Claricpp)

    } // namespace Unexpected

} // namespace Utils::Error

#endif
