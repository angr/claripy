/**
 * @file
 * @brief This file defines BigInt modes
 */
#ifndef R_SRC_MODE_BIGINT_HPP_
#define R_SRC_MODE_BIGINT_HPP_

#include <ostream>

namespace Mode {

    /** A mask used to define the type of comparison to be used */
    enum class BigInt { Str, Int };

    /** Ostream operator for Mode::BigInt */
    inline std::ostream &operator<<(std::ostream &os, const BigInt &b) {
        return os << "Mode::BigInt::" << ((b == BigInt::Int) ? "Int" : "Str");
    }

} // namespace Mode

#endif
