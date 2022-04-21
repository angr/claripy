/**
 * @file
 * \ingroup unittest
 */
#include <iostream>
#include <sstream>
#include <testlib/testlib.hpp>

/** A custom log type */
UTIL_LOG_DEFINE_LOG_CLASS(Custom)

/** Define test_each_level with the custom log type */
#define TEMPLATE_MACRO <Custom>
#include "test_each_level.hpp"


namespace L = Util::Log;
using Lvl = L::Level::Lvl;
using namespace UnitTest::TestLib;

/** A macro used for consistency */
#define MSG "Custom message"


/** Test the given logging function */
void test(std::shared_ptr<std::ostringstream> &s, Lvl) {
    const auto str { s->str() };
    UNITTEST_ASSERT(str == MSG "\n");
    s->str(""); // Clear the log for the next test
}

/** Create a style class */
struct CustomSty final : L::Style::Base {
    /** Name */
    [[nodiscard]] inline const char *name() const noexcept final { return "CustomSty"; }
    /** The style function */
    std::string str(CCSC, const Lvl, std::string &&) const final { return MSG; }
};

/** Each construction should have a unique pointer */
void custom() {
    // Configure backend and style to output to with all relevant info
    auto s { std::make_shared<std::ostringstream>() };
    Style::set<CustomSty>();
    L::Backend::set<L::Backend::OStream>(Util::PCast::Static::up<std::ostream>(s), true);

    // Clear the log for the next test
    s->str("");

    // Test each level
    UnitTest::test_each_level(s, test, "");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(custom)
