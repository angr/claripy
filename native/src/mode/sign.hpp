/**
 * @file
 * @brief This file defines Sign mask
 */
#ifndef R_SRC_MODE_SIGN_HPP_
#define R_SRC_MODE_SIGN_HPP_

#include "../util.hpp"


namespace Mode::Sign {

    /** An Sign enum with an underlying signed value where non-signed-ness is disallowed
     *  The underlying values of the enum values are 1 and -1
     *  signed specifier is required for cross-platform support
     */
    enum class FP : signed char { Minus = -1, Plus = 1 };

    /** An Sign enum with an underlying signed value where non-signed-ness is allowed
     *  The underlying values of the enum values are 1, -1, and 0
     *  signed specifier is required for cross-platform support
     */
    enum class Real : signed char { Minus = -1, None = 0, Plus = 1 };

    /** Convert an FP to a Real */
    constexpr Real to_real(const FP f) {
        return static_cast<Real>(Util::to_underlying(f));
    }

} // namespace Mode::Sign

#endif
