/**
 * @file
 * \ingroup utils
 * @brief This file contains the possible exceptions that indicate an internal claricpp failure
 * These exceptions are not expected to be raised if claricpp is operating as intended
 */
#ifndef R_UTILS_ERROR_UNEXPECTED_HPP_
#define R_UTILS_ERROR_UNEXPECTED_HPP_

#include "claricpp.hpp"


namespace Utils::Error::Unexpected {

    /** Base unexpected exception
     *  All unexpected exceptions must derive from this
     */
    DEFINE_NONFINAL_EXCEPTION(Base, Claricpp);

    /** Hash Collision exception */
    DEFINE_NONFINAL_EXCEPTION(Collision, Base);

    /** Null pointer exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Null, Base);

    /** Invalid path exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(BadPath, Base);

    /** Syscall failure exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Syscall, Base);

    /** Bad size exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Size, Base);

    /** Bad cast exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(BadCast, Base);

    /** Hash Collision exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(HashCollision, Collision);

    /** Bad variant access exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(BadVariantAccess, Base);

    /** Raised when a virtual function that should have been overridden was called */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(MissingVirtualFunction, Claricpp);

    /** Raised when a function is given invalid arguments */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Usage, Claricpp);

    /** Raised when a recurrence guarded function recurses too many times */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(RecurrenceLimit, Claricpp);

    /** Raised when something unknown occurs */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Unknown, Claricpp);

    /** Raised when an unsupported op is invoked */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(NotSupported, Claricpp);

    /** Raised when a dynamic type error occurs */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Type, Claricpp);

} // namespace Utils::Error::Unexpected

#endif
