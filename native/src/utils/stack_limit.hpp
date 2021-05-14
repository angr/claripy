/**
 * @file
 * \ingroup utils
 * @brief This file defines methods for adjusting the stack size
 * Note that we do not inline these functions since they require
 * C headers that would polute the global namespace
 */
#ifndef R_UTILS_STACKLIMIT_HPP_
#define R_UTILS_STACKLIMIT_HPP_

#include "macros.hpp"


namespace Utils::StackLimit {

    /** true iff stack limit operations are supported */
    UTILS_ICCBOOL supported {
#if __has_include(<sys/resource.h>)
        true
#else
        false
#endif
    };

    /** Get the stack limit
     *  Will throw an exception if the system does not support this
     */
    unsigned long long get();

    /** Get the max stack limit
     *  Will throw an exception if the system does not support this
     */
    unsigned long long max();

    /** Set the stack limit
     *  Will throw an exception if the system does not support this
     */
    void set(const unsigned long long to);

} // namespace Utils::StackLimit

#endif
