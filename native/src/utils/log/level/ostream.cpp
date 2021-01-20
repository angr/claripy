/**
 * @file
 * \ingroup utils
 */
#include "ostream.hpp"

#include "../../affirm.hpp"
#include "../../error/unexpected.hpp"

#include <map>


// For brevity
using namespace Utils;
using namespace Log;
using namespace Error::Unexpected;
using Lvl = Level::Level;


/** Create a map entry for a log level */
#define MAP_ENTRY(X) { Lvl::X, std::string(#X) },


/** Map Levels to their names */
static const std::map<Lvl, std::string> names = { MAP_ENTRY(Verbose) MAP_ENTRY(Debug) MAP_ENTRY(
    Info) MAP_ENTRY(Warning) MAP_ENTRY(Error) MAP_ENTRY(Critical) MAP_ENTRY(Disabled) };


std::ostream &operator<<(std::ostream &os, const Lvl &l) {
    const auto it = names.find(l);
    Utils::affirm<IncorrectUsage>(it != names.end(), "Unknown level passed to << operator");
    os << it->second;
    return os;
}
