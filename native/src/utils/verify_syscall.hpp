/**
 * @file
 * \ingroup utils
 * @brief Verifies the syscall return code, raises an informative exception if it is invalid
 */
#ifndef __UTILS_VERIFYSYSCALL_HPP__
#define __UTILS_VERIFYSYSCALL_HPP__

#include "error.hpp"


namespace Utils {

    /** Verifies the syscall return code
     *  Raises an informative exception if it is invalid
     */
    inline void verify_syscall(const int rv) {
        if (rv != 0) {
            throw Utils::Error::Unexpected::Syscall(
                WHOAMI_WITH_SOURCE, "getrlimit() failed with error: ", std::strerror(errno));
        }
    }

} // namespace Utils

#endif
