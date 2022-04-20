/**
 * @file
 * \ingroup util
 * @brief This file defines methods for adjusting the stack size
 * Note that we do not inline these functions since they require
 * C headers which would pollute the global namespace
 */
#ifndef R_SRC_UTIL_STACKLIMIT_HPP_
#define R_SRC_UTIL_STACKLIMIT_HPP_

#include "macros.hpp"


// Determine if <sys/resource.h> exists
#if defined(__has_include)
    #if __has_include(<sys/resource.h>)
        /** Note that we do have <sys/resource.h> */
        #define UTIL_HASSYSRESOURCE
    #endif
#endif


namespace Util::StackLimit {

    /** true iff stack limit operations are supported */
    UTIL_ICCBOOL supported {
#ifdef UTIL_HASSYSRESOURCE
        true
#else
        false
#endif
    };

    /** The unsigned type StackLimit functions take */
    using ULL = unsigned long long;

    /** Get the stack limit
     *  Will throw an exception if the system does not support this
     */
    ULL get();

    /** Get the max stack limit
     *  Will throw an exception if the system does not support this
     */
    ULL max();

    /** Set the stack limit
     *  Will throw an exception if the system does not support this
     */
    void set(const ULL to);

} // namespace Util::StackLimit

#endif
