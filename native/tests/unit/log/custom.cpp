/** @file */

#include "src/utils.hpp"

#include <iostream>
#include <sstream>


using namespace Utils::Log;
using Lvl = Level::Level;


const std::string cst("Custom");


/** Test the given logging function */
int test(std::ostringstream &s) {
    auto str = s.str();
    str.pop_back(); // newline
    if (str == cst) {
        s.str("");
        return 0;
    }
    else {
        return 1;
    }
}

/** Create a style class */
struct CustomSty : Style::AbstractBase {
    /** The style function */
    std::string str(Constants::CCSC, const Lvl &, const std::ostringstream &) override {
        return cst;
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
