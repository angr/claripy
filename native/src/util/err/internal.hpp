/**
 * @file
 * \ingroup util
 * @brief This file contains the possible exceptions that indicate an internal claricpp failure
 * These exceptions are not expected to be raised if claricpp is operating as intended
 */
#ifndef R_SRC_UTIL_ERR_INTERNAL_HPP_
#define R_SRC_UTIL_ERR_INTERNAL_HPP_

#include "claricpp.hpp"


namespace Util::Err {

    /** Base unexpected exception
     *  All unexpected exceptions must derive from this
     */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Internal, Claricpp);

    /** Hash Collision exception */
    UTIL_ERR_DEFINE_NONFINAL_EXCEPTION(Collision, Internal);

    /** Null pointer exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Null, Internal);

    /** Invalid path exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(BadPath, Internal);

    /** Syscall failure exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Syscall, Internal);

    /** Bad size exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Size, Internal);

    /** Bad index exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Index, Internal);

    /** Bad cast exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(BadCast, Internal);

    /** Hash Collision exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(HashCollision, Collision);

    /** Bad variant access exception */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(BadVariantAccess, Internal);

    /** Raised when a virtual function that should have been overridden was called */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(MissingVirtualFunction, Internal);

    /** Raised when a function is given invalid arguments */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Usage, Internal);

    /** Raised when a recurrence guarded function recurses too many times */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(RecurrenceLimit, Internal);

    /** Raised when something unknown occurs */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Unknown, Internal);

    /** Raised when an unsupported op is invoked */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(NotSupported, Internal);

    /** Raised when a dynamic type error occurs */
    UTIL_ERR_DEFINE_FINAL_EXCEPTION(Type, Internal);

} // namespace Util::Err

#endif
