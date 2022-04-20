/**
 * @file
 * @brief This file defines Shift mask
 */
#ifndef R_SRC_MODE_SHIFT_HPP_
#define R_SRC_MODE_SHIFT_HPP_

namespace Mode {

    /** A mask used to describe a type of bit shift */
    enum class Shift { Left, LogicalRight, ArithmeticRight };

    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const Shift &m) {
        switch (m) {
            case Shift::Left:
                return os << "Left";
            case Shift::LogicalRight:
                return os << "Logical-Right";
            case Shift::ArithmeticRight:
                return os << "Arithmetic-Right";
            default:
                return os << "Invalid";
        }
    }

} // namespace Mode

#endif
