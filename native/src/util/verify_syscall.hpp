/**
 * @file
 * \ingroup util
 * @brief Verifies the syscall return code, raises an informative exception if it is invalid
 */
#ifndef R_SRC_UTIL_VERIFYSYSCALL_HPP_
#define R_SRC_UTIL_VERIFYSYSCALL_HPP_

#include "assert.hpp"
#include "err.hpp"

#include <cstring>


namespace Util {

    /** Verifies the syscall return code
     *  Raises an informative exception if it is invalid
     */
    inline void verify_syscall(const int rv) {
        UTIL_ASSERT(Util::Err::Syscall, rv == 0,
                    "getrlimit() failed with error: ", std::strerror(errno));
    }

} // namespace Util

#endif
