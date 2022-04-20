/**
 * @file
 * @brief This file defines LR mode
 */
#ifndef R_SRC_MODE_LR_HPP_
#define R_SRC_MODE_LR_HPP_

#include <ostream>

namespace Mode {

    /** A mask used to denote Left or Right */
    enum class LR { Left, Right };

    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const LR &m) {
        return os << (m == LR::Left ? "Left" : "Right");
    }

} // namespace Mode

#endif
