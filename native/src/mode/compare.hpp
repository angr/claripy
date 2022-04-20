/**
 * @file
 * @brief This file defines Compare mask
 */
#ifndef R_SRC_MODE_COMPARE_HPP_
#define R_SRC_MODE_COMPARE_HPP_

#include "../util.hpp"

#include <ostream>


namespace Mode {
    /** A mask used to define the type of comparison to be used */
    enum class Compare { UGE = 0, UGT, ULE, ULT, SGE = 4, SGT, SLE, SLT };

    /** Return true iff a Compare is signed */
    constexpr bool is_signed(const Compare c) {
        return c >= Compare::SGE;
    }

    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const Compare &c) {
        constexpr CCSC strs[] { "UGE", "UGT", "ULE", "ULT", "SGE", "SGT", "SLE", "SLT" };
        os << "Mode::Compare(" << strs[Util::to_underlying(c)] << ")";
        return os;
    }
} // namespace Mode

#endif
