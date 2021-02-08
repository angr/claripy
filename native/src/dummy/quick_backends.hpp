/**
 * @file
 * @brief Replace this file with proper python hooks
 */
#ifndef __DUMMY_QUICKBACKENDS_HPP__
#define __DUMMY_QUICKBACKENDS_HPP__

#include <array>


namespace Dummy {

    bool echo(const bool set = false, const bool value = true) {
        static bool b = false;
        if (set) {
            b = value;
        }
        return b;
    }
    bool echo_wrap() { return echo(); }

    constexpr std::array<bool(), 1> quick_backends { echo_wrap };

} // namespace Dummy

#endif
