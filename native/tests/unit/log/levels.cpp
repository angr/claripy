/** @file */

#include "utils.hpp"

#include <iostream>
#include <sstream>


using namespace Utils::Log;
using Lvl = Level::Level;


/** Test the given logging function */
#define STR "log test"
int test(std::ostringstream &s) {
    auto str = s.str();
    if (str.find(STR) == std::string::npos) {
        return 1;
    }
    else {
        s.str("");
        return 0;
    }
}


/** Each construction should have a unique pointer */
int levels() {
    // Configure backend and style to output to with all relevant info
    std::ostringstream s;
    Style::set<Style::LevelTimestampMessage>();
    Backend::set<Backend::OStream>(s);

    const UTILS_LOG_LEVEL_CONSTANT auto lvl = Level::get();

    // Test each level
    if UTILS_LOG_LEVEL_CONSTANT
        UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Critical) {
            critical(STR);
            if (test(s) == 1) {
                return 1;
            }
        }
    if UTILS_LOG_LEVEL_CONSTANT
        UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Error) {
            error(STR);
            if (test(s) == 1) {
                return 1;
            }
        }
    if UTILS_LOG_LEVEL_CONSTANT
        UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Warning) {
            warning(STR);
            if (test(s) == 1) {
                return 1;
            }
        }
    if UTILS_LOG_LEVEL_CONSTANT
        UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Info) {
            info(STR);
            if (test(s) == 1) {
                return 1;
            }
        }
    if UTILS_LOG_LEVEL_CONSTANT
        UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Debug) {
            debug(STR);
            if (test(s) == 1) {
                return 1;
            }
        }
    if UTILS_LOG_LEVEL_CONSTANT
        UTILS_LOG_LEVEL_IMPLIES(lvl, Lvl::Verbose) {
            verbose(STR);
            if (test(s) == 1) {
                return 1;
            }
        }

    return 0;
}
