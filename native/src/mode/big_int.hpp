/**
 * @file
 * @brief This file defines BigInt modes
 */
#ifndef R_MODE_BIGINT_HPP_
#define R_MODE_BIGINT_HPP_

extern "C" {
#include "big_int.h"
};
#include <ostream>

namespace Mode {

    /** A mask used to define the type of comparison to be used */
    enum class BigInt { MODE_BIGINT_VALS() };

    /** Ostream operator for Mode::BigInt */
    inline std::ostream &operator<<(std::ostream &os, const BigInt &b) {
        return os << "Mode::BigInt::" << ((b == BigInt::Int) ? "Int" : "Str");
    }

} // namespace Mode

#endif
