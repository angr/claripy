/**
 * @file
 * \ingroup util
 * @brief This file declares Backtrace generators
 */
#ifndef R_SRC_UTIL_BACKTRACE_GENERATORS_HPP_
#define R_SRC_UTIL_BACKTRACE_GENERATORS_HPP_

#include "../../constants.hpp"

#include <ostream>

namespace Util::Backtrace {
    /** Adds a source root for backward to use */
    void add_source_root(CCSC native_dir);
    /** A backtrace generator which uses backward */
    void backward(std::ostream &o, const unsigned ignore_frames, const int16_t max_frames) noexcept;
} // namespace Util::Backtrace

#endif