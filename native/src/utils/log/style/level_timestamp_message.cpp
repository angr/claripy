/**
 * @file
 * \ingroup utils
 */
#include "level_timestamp_message.hpp"

#include "../../affirm_not_null_debug.hpp"
#include "../../ansi_color_codes.hpp"

#include <ctime>
#include <iomanip>
#include <mutex>
#include <sstream>


// For brevity
using namespace Utils;
using namespace Log;
using namespace Style;
using Lvl = Level::Level;


/** Get the current local time */
static auto get_time() {
    static std::mutex m;
    const auto t { std::time(nullptr) };
    std::unique_lock<decltype(m)> rw { m };
    return *std::localtime(&t); // NOLINT (this is a thread-unsafe function)
}

// Return "<level>: <timestamp>: <raw>"
std::string LevelTimestampMessage::str(Constants::CCSC, const Lvl &lvl,
                                       const std::ostringstream &raw) const {
    // Color label
    const char *color { nullptr };
    switch (lvl) {
        case Lvl::Verbose:
            color = ANSIColorCodes::wht;
            break;
        case Lvl::Info:
            color = ANSIColorCodes::blu;
            break;
        case Lvl::Warning:
            color = ANSIColorCodes::yel;
            break;
        case Lvl::Error:
            color = ANSIColorCodes::Bold::mag;
            break;
        case Lvl::Critical:
            color = ANSIColorCodes::HighIntensity::Bold::red;
            break;
        case Lvl::Debug:
            color = ANSIColorCodes::blk;
            break;
        case Lvl::Disabled: // Should not be possible
            throw Error::Unexpected::Usage("Log backend given disabled level");
            break;
        default: // Should not be possible
            throw Error::Unexpected::Unknown("Logger was given unknown level");
            break;
    }
    UTILS_AFFIRM_NOT_NULL_DEBUG(color);

    // Get time
    const auto tm { get_time() };

    // Output
    std::ostringstream ret;
    ret << color << lvl << ANSIColorCodes::blk << ": " << std::put_time(&tm, "%c %Z") << " -- "
        << raw.str();
    return ret.str();
}
