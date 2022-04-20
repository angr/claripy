/**
 * @file
 * \ingroup util
 * @brief This file defines a method to end the program
 */
#ifndef R_SRC_UTIL_TERMINATE_HPP_
#define R_SRC_UTIL_TERMINATE_HPP_

#include "../constants.hpp"

namespace Util {
    /** Terminates the program */
    [[noreturn]] void terminate(CCSC msg = nullptr, const bool force_flush_log = false) noexcept;
} // namespace Util

#endif