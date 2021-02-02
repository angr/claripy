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
            inline virtual ~Base();
        };

        /** Default virtual destructor */
        Base::~Base() = default;

        /** Bad cast exception */
        DEFINE_SUBCLASS_WITH_CTOR(BadCast, Base)

        /** Raised when a function is given invalid arguments */
        DEFINE_SUBCLASS_WITH_CTOR(IncorrectUsage, Claricpp)

        /** Raised when a recurrence gaurded function recurrses too many times */
        DEFINE_SUBCLASS_WITH_CTOR(RecurrenceLimit, Claricpp)

        /** Raised when something unknown occurs */
        DEFINE_SUBCLASS_WITH_CTOR(Unknown, Claricpp)

    } // namespace Unexpected

} // namespace Utils::Error

#endif
