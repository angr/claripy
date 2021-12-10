/**
 * @file
 * \ingroup util
 * @brief This file defines a method to end the program
 */
#ifndef R_UTIL_TERMINATE_HPP_
#define R_UTIL_TERMINATE_HPP_

namespace Util {
    /** Terminates the program */
    [[noreturn]] void terminate(const bool force_flush_log = false) noexcept;
} // namespace Util

#endif