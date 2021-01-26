/**
 * @file
 * \ingroup utils
 */
#include "level_timestamp_message.hpp"

#include "../../ansi_color_codes.hpp"
#include "../../error/unexpected.hpp"

#include <ctime>
#include <iomanip>
#include <sstream>


// For brevity
using namespace Utils;
using namespace Log;
using namespace Style;
using Lvl = Level::Level;


// Return "<level>: <timestamp>: <raw>"
std::string LevelTimestampMessage::str(Constants::CCSC, const Lvl &lvl,
                                       const std::ostringstream &raw) {

    // Get time
    const auto t = std::time(nullptr);
    const auto tm = *std::localtime(&t);

    // Color label
    const char *color;
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
        throw Error::Unexpected::IncorrectUsage("Log backend given disabled level");
        break;
    default: // Just in case
        throw Error::Unexpected::Unknown("Logger was given unknown level");
        break;
    }

    // Output
    std::ostringstream ret;
    ret << color << lvl << ANSIColorCodes::blk << ": " << std::put_time(&tm, "%c %Z") << " -- "
        << raw.str();
    return ret.str();
}
