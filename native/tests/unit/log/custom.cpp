/** @file */

#include "test_each_level.hpp"
#include "testlib.hpp"
#include "utils.hpp"

#include <iostream>
#include <sstream>


using namespace Utils::Log;
using Lvl = Level::Level;
using namespace UnitTest::TestLib;


const std::string cst("Custom");


/** Test the given logging function */
void test(std::ostringstream &s) {
    auto str = s.str();
    str.pop_back(); // newline
    UNITTEST_ASSERT(str == cst)
    s.str(""); // clear the log for the next test
}

/** Create a style class */
struct CustomSty : Style::AbstractBase {
    /** The style function */
    std::string str(Constants::CCSC, const Lvl &, const std::ostringstream &) override {
        return cst;
    }
};

/** A custom log type */
UTILS_LOG_DEFINE_LOG_CLASS(Custom)


/** Each construction should have a unique pointer */
int custom() {
    // Configure backend and style to output to with all relevant info
    std::ostringstream s;
    Style::set<CustomSty>();
    Backend::set<Backend::OStream>(s);

    // Test each level
    UnitTest::test_each_level(s, test, "");
    return 0;
}
