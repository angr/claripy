/** @file */
#include "level_map.hpp"

// For brevity
using namespace Utils;
using namespace Log;


const std::map<Level, const char *const> Log::level_map = {
    { Level::Debug, "Debug" },     { Level::Verbose, "Verbose" }, { Level::Info, "Info" },
    { Level::Warning, "Warning" }, { Level::Error, "Error" },     { Level::Critical, "Critical" },
};
