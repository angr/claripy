/**
 * @file
 * @brief This file defines Sign mask
 */
#ifndef R_MODE_SIGN_HPP_
#define R_MODE_SIGN_HPP_

namespace Mode {

    /** An Sign enum with an underlying signed value
     *  The underlying values of the enum values are 1 and -1
     */
    enum class Sign : char { Minus = -1, Plus = 1 };

} // namespace Mode

#endif
