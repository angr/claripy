/**
 * @file
 * \ingroup util
 * @brief This file defines a method of backtracing the stack using Backward
 */
#ifndef R_UTIL_BACKTRACE_BACKWARD_HPP_
#define R_UTIL_BACKTRACE_BACKWARD_HPP_

#include "../../constants.hpp"

#include <ostream>


namespace Util::Backtrace {

    /** Save a backtrace to o using Backward */
    void backward(std::ostream &o, const UInt ignore_frames = 0,
                  const int16_t max_frames = 0x1000) noexcept;
} // namespace Util::Backtrace

#endif
