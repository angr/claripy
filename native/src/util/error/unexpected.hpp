/**
 * @file
 * \ingroup util
 * @brief This file contains the possible exceptions that indicate an internal claricpp failure
 * These exceptions are not expected to be raised if claricpp is operating as intended
 */
#ifndef R_UTIL_ERROR_UNEXPECTED_HPP_
#define R_UTIL_ERROR_UNEXPECTED_HPP_

#include "claricpp.hpp"


namespace Util::Error {

    /** Base unexpected exception
     *  All unexpected exceptions must derive from this
     */
    DEFINE_NONFINAL_EXCEPTION(Unexpected, Claricpp);

    /** Hash Collision exception */
    DEFINE_NONFINAL_EXCEPTION(Collision, Unexpected);

    /** Null pointer exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Null, Unexpected);

    /** Invalid path exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(BadPath, Unexpected);

    /** Syscall failure exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Syscall, Unexpected);

    /** Bad size exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(Size, Unexpected);

    /** Bad cast exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(BadCast, Unexpected);

    /** Hash Collision exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(HashCollision, Collision);

    /** Bad variant access exception */
    DEFINE_FINAL_SUBCLASS_USING_CTOR(BadVariantAccess, Unexpected);

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

} // namespace Util::Error

#endif
