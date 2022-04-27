/**
 * @file
 * \ingroup util
 * @brief This file defines a way to enable backtrace support on signals
 */
#ifndef R_SRC_UTIL_BACKTRACE_HANDLESIGNALS_HPP_
#define R_SRC_UTIL_BACKTRACE_HANDLESIGNALS_HPP_

#include <atomic>

namespace Util::Backtrace {
    /** Enable signal handling so backtraces are printed on signals */
    void handle_signals();
} // namespace Util::Backtrace

#endif
