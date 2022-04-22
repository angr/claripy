/**
 * @file
 * \ingroup util
 */
#include "level_timestamp_message.hpp"

#include "../../ansi_color_codes.hpp"
#include "../../assert_not_null_debug.hpp"

#include <ctime>
#include <iomanip>
#include <mutex>
#include <sstream>


// For brevity
using namespace Util;
using namespace Log;
using namespace Style;


/** Get the current local time */
static auto get_time() {
    static std::mutex m;
    const auto t { std::time(nullptr) };
    std::unique_lock<decltype(m)> rw { m };
    return *std::localtime(&t); // NOLINT (not threadsafe, hence lock)
}

// Return "<level>: <timestamp>: <raw>"
std::string LevelTimestampMessage::str(CCSC, const Level::Lvl l, std::string &&raw) const {
    // Color label
    const char *color { nullptr };
    switch (l.lvl) {
#define M_CASE(LVL, COLOR)                                                                         \
    case Level::LVL.lvl:                                                                           \
        color = ANSIColorCodes::COLOR;                                                             \
        break
        M_CASE(verbose, wht);
        M_CASE(debug, blk);
        M_CASE(info, blu);
        M_CASE(warning, yel);
        M_CASE(error, Bold::mag);
        M_CASE(critical, HighIntensity::Bold::red);
#undef M_CASE
        case Level::disabled.lvl: // Should not be possible
            UTIL_THROW(Err::Usage, "Log backend given disabled level");
        default: // Should not be possible
            UTIL_THROW(Err::Unknown, "Logger was given unknown level");
    }
    UTIL_ASSERT_NOT_NULL_DEBUG(color);

    // Get time
    const auto tm { get_time() };

    // Output
    std::ostringstream ret;
    ret << color << l << ANSIColorCodes::reset << ": " << std::put_time(&tm, "%c %Z") << " -- "
        << std::move(raw); // NOLINT (std::move might not move if << takes const ref)
    return ret.str();
}
