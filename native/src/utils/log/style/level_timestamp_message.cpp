/** @file */
#include "level_timestamp_message.hpp"

#include "../../../errors/unexpected.hpp"
#include "../../affirm.hpp"
#include "../../ansi_color_codes.hpp"
#include "../level_map.hpp"

#include <ctime>
#include <iomanip>
#include <sstream>


// For brevity
using namespace Utils;
using namespace Log;
using namespace Style;
using namespace Errors::Unexpected;


inline const char *name(const Level &lvl, Constants::CCSC fname) {
    const auto it = level_map.find(lvl);
    affirm<IncorrectUsage>(it != level_map.end(), __FILE__ ": ", fname, " given unknown level.");
    return it->second;
}

// Return "<level>: <timestamp>: <raw>"
std::string LevelTimestampMessage::str(Constants::CCSC, const Level &lvl,
                                       const std::ostringstream &raw) {
    // Get time
    const auto t = std::time(nullptr);
    const auto tm = *std::localtime(&t);
    // Color label
    const char *color;
    switch (lvl) {
    case Level::Verbose:
        color = ANSIColorCodes::wht;
    case Level::Info:
        color = ANSIColorCodes::blu;
    case Level::Warning:
        color = ANSIColorCodes::yel;
    case Level::Error:
        color = ANSIColorCodes::Bold::mag;
    case Level::Critical:
        color = ANSIColorCodes::HighIntensity::Bold::red;
    default:
        color = ANSIColorCodes::blk;
    }

    // Output
    std::ostringstream ret;
    ret << color << name(lvl, __func__) << ANSIColorCodes::blk << ": "
        << std::put_time(&tm, "%c %Z") << " -- " << raw.str();
    return ret.str();
}
