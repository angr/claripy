/**
 * @file
 * \ingroup util
 * @brief This file defines log level modes
 */
#ifndef R_SRC_UTIL_LOG_LEVEL_LEVEL_HPP_
#define R_SRC_UTIL_LOG_LEVEL_LEVEL_HPP_

#include "../../../constants.hpp"
#include "../../../macros.hpp"
#include "../../widen.hpp"

#include <cstdint>
#include <limits>
#include <ostream>


#ifdef CONSTANT_LOG_LEVEL
    /** Constexpr if and only if the log level is immutable */
    #define UTIL_LOG_LEVEL_CONSTEXPR constexpr
#else
    /** Constexpr if and only if the log level is immutable */
    #define UTIL_LOG_LEVEL_CONSTEXPR
#endif

#include <iostream>

namespace Util::Log::Level {

    /** The log level type */
    struct Lvl final {
        /** The level type */
        using Raw = uint_fast8_t;
        /** Level */
        Raw lvl;
    };

    // Predefined levels

    /** A verbose log level */
    static const constexpr Lvl verbose { 0 };
    /** A debug log level */
    static const constexpr Lvl debug { 10 };
    /** An info log level */
    static const constexpr Lvl info { 20 };
    /** A warning log level */
    static const constexpr Lvl warning { 30 };
    /** An error log level */
    static const constexpr Lvl error { 40 };
    /** A critical log level */
    static const constexpr Lvl critical { 50 };
    /** A disabled log level */
    static const constexpr Lvl disabled { std::numeric_limits<Lvl::Raw>::max() };

    // Operators

    /** Log level equality */
    constexpr bool operator==(const Lvl &a, const Lvl &b) noexcept {
        return a.lvl == b.lvl;
    }
    /** Log level anti-equality */
    constexpr bool operator!=(const Lvl &a, const Lvl &b) noexcept {
        return a.lvl != b.lvl;
    }
    /** Stream operator */
    inline std::ostream &operator<<(std::ostream &os, const Lvl &l) {
        static const constexpr CCSC defaults[] { "Verbose", "Debug", "Info",
                                                 "Warning", "Error", "Critical" };
        if (LIKELY(l.lvl % 10 == 0 && l.lvl <= critical.lvl)) {
            return os << defaults[l.lvl / 10];
        }
        else if (l == disabled) {
            return os << "Disabled";
        }
        else {
            // Widen in case of unsigned char
            return os << "<Log level: " << widen<U64>(l.lvl) << '>';
        }
    }

} // namespace Util::Log::Level

#endif
