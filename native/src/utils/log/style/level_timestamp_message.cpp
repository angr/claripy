/** @file */
#include "level_timestamp_message.hpp"

#include "../../../errors/unexpected.hpp"
#include "../../affirm.hpp"
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
    // Output
    std::ostringstream ret;
    ret << name(lvl, __func__) << ": " << std::put_time(&tm, "%c %Z") << " -- " << raw.str();
    return ret.str();
}
