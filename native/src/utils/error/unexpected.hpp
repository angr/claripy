/**
 * @file
 * \ingroup utils
 * @brief This file contains the possible exceptions that indicate an internal claricpp failur
 * These exceptions are not expected to be raised if claricpp is operating as intended
 * Note: these exceptions ignore the rule of 5 (see claricpp.hpp)
 */
#ifndef __UTILS_ERROR_UNEXPECTED_HPP__
#define __UTILS_ERROR_UNEXPECTED_HPP__

#include "claricpp.hpp"


namespace Utils::Error {

    // Errors that indicate a code issue
    // These should never be thrown unless a claricpp bug occurs
    namespace Unexpected {

        /** Base unexpected exception
         *  All unexpected exceptions must derive from this
         */
        DEFINE_NONFINAL_INSTANTIABLE_SUBCLASS_WITH_CTOR(Base, Claricpp)

        /** Bad size exception */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Size, Base)

        /** Bad cast exception */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(BadCast, Base)

        /** Raised when a function is given invalid arguments */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(IncorrectUsage, Claricpp)

        /** Raised when a recurrence gaurded function recurrses too many times */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(RecurrenceLimit, Claricpp)

        /** Raised when something unknown occurs */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Unknown, Claricpp)

        /** Raised when a dynamic type error occurs */
        DEFINE_FINAL_SUBCLASS_WITH_CTOR(Type, Claricpp)

    } // namespace Unexpected

} // namespace Utils::Error

#endif
