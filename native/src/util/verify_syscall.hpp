/**
 * @file
 * \ingroup util
 * @brief Verifies the syscall return code, raises an informative exception if it is invalid
 */
#ifndef R_UTIL_VERIFYSYSCALL_HPP_
#define R_UTIL_VERIFYSYSCALL_HPP_

#include "error.hpp"

#include <cstring>


namespace Util {

    /** Verifies the syscall return code
     *  Raises an informative exception if it is invalid
     */
    inline void verify_syscall(const int rv) {
        if (rv != 0) {
            throw Util::Error::Unexpected::Syscall(
                WHOAMI_WITH_SOURCE, "getrlimit() failed with error: ", std::strerror(errno));
        }
    }

} // namespace Util

#endif
