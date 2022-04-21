/**
 * @file
 * \ingroup util
 * @brief This file declares Backtrace generators
 */
#ifndef R_SRC_UTIL_BACKTRACE_GENERATORS_HPP_
#define R_SRC_UTIL_BACKTRACE_GENERATORS_HPP_

#include "constants.hpp"

namespace Util::Backtrace {
    /** A backtrace generator which uses backward */
    GeneratorFunc backward;
#if 0 // See comments in native.cpp for why
    /** A backtrace generator rolled natively */
    GeneratorFunc native;
#endif
} // namespace Util::Backtrace

#endif