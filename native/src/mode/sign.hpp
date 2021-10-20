/**
 * @file
 * @brief This file defines Sign mask
 */
#ifndef R_MODE_SIGN_HPP_
#define R_MODE_SIGN_HPP_

#include "../util.hpp"


namespace Mode::Sign {

    /** An Sign enum with an underlying signed value where non-signed-ness is disallowed
     *  The underlying values of the enum values are 1 and -1
     */
    enum class FP : char { Minus = -1, Plus = 1 };

    /** An Sign enum with an underlying signed value where non-signed-ness is allowed
     *  The underlying values of the enum values are 1, -1, and 0
     */
    enum class Real : char { Minus = -1, None = 0, Plus = 1 };

    /** Convert an FP to a Real */
    constexpr Real to_real(const FP f) { return static_cast<Real>(Util::to_underlying(f)); }

} // namespace Mode::Sign

#endif
