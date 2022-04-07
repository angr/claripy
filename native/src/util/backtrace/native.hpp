/**
 * @file
 * \ingroup util
 * @brief This file defines a native method of backtracing the stack
 */
#ifndef R_UTIL_BACKTRACE_NATIVE_HPP_
#define R_UTIL_BACKTRACE_NATIVE_HPP_

#include "../../constants.hpp"

#include <ostream>

namespace Util::Backtrace::Trace {
    struct Native final {
        /** Save a backtrace to o */
        static void gen(std::ostream &o, const unsigned ignore_frames,
                        const int16_t max_frames) noexcept;
    };
} // namespace Util::Backtrace::Trace

#endif
