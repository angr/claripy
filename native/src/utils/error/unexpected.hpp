/**
 * @file
 * \ingroup utils
 * @brief This file contains the possible exceptions that indicate an internal claricpp failur
 * These exceptions are not expected to be raised if claricpp is operating as intended
 */
#ifndef __UTILS_ERROR_UNEXPECTED_HPP__
#define __UTILS_ERROR_UNEXPECTED_HPP__

#include "claricpp.hpp"


namespace Utils::Error::Unexpected {

    /** Base unexpected exception
     *  All unexpected exceptions must derive from this
     */
    DEFINE_NONFINAL_EXCEPTION(Base, Claricpp);

    /** Syscall failure exception */
    DEFINE_FINAL_EXCEPTION(Syscall, Base);

    /** Bad size exception */
    DEFINE_FINAL_EXCEPTION(Size, Base);

    /** Bad cast exception */
    DEFINE_FINAL_EXCEPTION(BadCast, Base);

    /** Bad variant access exception */
    DEFINE_FINAL_EXCEPTION(BadVariantAccess, Base);

    /** Raised when a virtual function that should have been overriden was called */
    DEFINE_FINAL_EXCEPTION(MissingVirtualFunction, Claricpp);

    /** Raised when a function is given invalid arguments */
    DEFINE_FINAL_EXCEPTION(IncorrectUsage, Claricpp);

    /** Raised when a recurrence gaurded function recurrses too many times */
    DEFINE_FINAL_EXCEPTION(RecurrenceLimit, Claricpp);

    /** Raised when something unknown occurs */
    DEFINE_FINAL_EXCEPTION(Unknown, Claricpp);

    /** Raised when an unsupported op is invoked */
    DEFINE_FINAL_EXCEPTION(NotSupported, Claricpp);

    /** Raised when a dynamic type error occurs */
    DEFINE_FINAL_EXCEPTION(Type, Claricpp);

} // namespace Utils::Error::Unexpected

#endif
