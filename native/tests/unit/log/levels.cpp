/** @file */

#include "src/utils.hpp"

#include <iostream>
#include <sstream>


using namespace Utils::Log;


/** Test the given logging function */
#define STR "log test"
int test(std::ostringstream &s) {
    auto str = s.str();
    if (str.find(STR) == std::string::npos) {
        return 1;
    }
    else {
        s.clear();
        return 0;
    }
}


/** Each construction should have a unique pointer */
int levels() {
    // Configure backend and style to output to with all relevant info
    std::ostringstream s;
    Style::set<Style::LevelTimestampMessage>();
    Backend::set<Backend::OStream>(s);

    // Test each level
    if constexpr (Private::Enabled::critical) {
        critical(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if constexpr (Private::Enabled::error) {
        error(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if constexpr (Private::Enabled::warning) {
        warning(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if constexpr (Private::Enabled::info) {
        info(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if constexpr (Private::Enabled::debug) {
        debug(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if constexpr (Private::Enabled::verbose) {
        verbose(STR);
        if (test(s) == 1) {
            return 1;
        }
    }

    return 0;
}
