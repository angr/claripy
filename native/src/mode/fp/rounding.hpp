/**
 * @file
 * @brief This file defines FP Rounding modes
 */
#ifndef R_SRC_MODE_FP_ROUNDING_HPP_
#define R_SRC_MODE_FP_ROUNDING_HPP_

#include "../../util.hpp"

#include <ostream>

namespace Mode::FP {
    /** FP modes supported by claripy */
    enum class Rounding {
        NearestTiesEven,
        NearestTiesAwayFromZero,
        TowardsZero,
        TowardsPositiveInf,
        TowardsNegativeInf
    };
    /** Rounding mode stream operator */
    inline std::ostream &operator<<(std::ostream &o, const Rounding &r) {
        return o << Util::to_underlying(r);
    }
} // namespace Mode::FP

#endif
