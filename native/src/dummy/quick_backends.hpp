/**
 * @file
 * @brief Replace this file with proper python hooks
 */
#ifndef R_DUMMY_QUICKBACKENDS_HPP_
#define R_DUMMY_QUICKBACKENDS_HPP_

#include "../constants.hpp"

#include <array>

// Forward declarations
namespace Expression {
    class Bool;
}

namespace Dummy {

    // Echo the last value of value
    inline bool echo(const bool set = false, const bool value = true) {
        static bool b = false;
        if (set) {
            b = value;
        }
        return b;
    }

    // A dummy backend
    struct Backend {
        static bool is_true(Constants::CTSC<Expression::Bool>) { return echo(); }
        static bool is_false(Constants::CTSC<Expression::Bool>) { return !echo(); }
    };

    // backends._quick_backends
    constexpr std::array<Backend, 1> quick_backends { Backend {} };

} // namespace Dummy

#endif
