/**
 * @file
 * \ingroup util
 * @brief This file defines constants useful for Backtrace
 */
#ifndef R_SRC_UTIL_BACKTRACE_CONSTANTS_HPP_
#define R_SRC_UTIL_BACKTRACE_CONSTANTS_HPP_

#include "../type.hpp"

#include <ostream>

namespace Util::Backtrace {
    /** The generator function type */
    using GeneratorFunc = void(std::ostream &o, const unsigned ignore_frames,
                               const int16_t max_frames) noexcept;
} // namespace Util::Backtrace

#endif
