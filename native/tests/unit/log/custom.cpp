/** @file */

#include "src/utils.hpp"

#include <iostream>
#include <sstream>


using namespace Utils::Log;


/** Test the given logging function */
int test(std::ostringstream &s) {
    auto str = s.str();
    std::cout << str;
    if (str.find("Custom") == std::string::npos) {
        return 1;
    }
    else {
        s.clear();
        return 0;
    }
}

/** Create a style class */
struct CustomSty : Style::AbstractBase {
    /** The style function */
    std::string str(Constants::CCSC custom, const Level &, const std::ostringstream &) override {
        return custom;
    }
};

//  A custom log type
UTILS_LOG_DEFINE_LOG_CLASS(Custom)

#define STR ""

/** Each construction should have a unique pointer */
int custom() {
    // Configure backend and style to output to with all relevant info
    std::ostringstream s;
    Style::set<CustomSty>();
    Backend::set<Backend::OStream>(s);

    // Test each level
    if RUNTIME_LOG_CONSTEXPR (Private::Enabled::critical) {
        critical<Custom>(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if RUNTIME_LOG_CONSTEXPR (Private::Enabled::error) {
        error<Custom>(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if RUNTIME_LOG_CONSTEXPR (Private::Enabled::warning) {
        warning<Custom>(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if RUNTIME_LOG_CONSTEXPR (Private::Enabled::info) {
        info<Custom>(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if RUNTIME_LOG_CONSTEXPR (Private::Enabled::debug) {
        debug<Custom>(STR);
        if (test(s) == 1) {
            return 1;
        }
    }
    if RUNTIME_LOG_CONSTEXPR (Private::Enabled::verbose) {
        verbose<Custom>(STR);
        if (test(s) == 1) {
            return 1;
        }
    }

    return 0;
}
