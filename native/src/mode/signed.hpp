/**
 * @file
 * @brief This file defines Signed mode
 */
#ifndef R_SRC_MODE_SIGNED_HPP_
#define R_SRC_MODE_SIGNED_HPP_

#include <ostream>

namespace Mode {

    /** A mask used to denote Signed or Unsigned */
    enum class Signed { Signed, Unsigned };

    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const Signed &m) {
        return os << (m == Signed::Signed ? "Signed" : "Unsigned");
    }

} // namespace Mode

#endif
