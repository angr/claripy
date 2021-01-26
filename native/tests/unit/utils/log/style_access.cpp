/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"


using namespace Utils::Log;
using namespace UnitTest::TestLib;


/** Create a style class */
struct Plain : Style::AbstractBase {
    /** The style function */
    std::string str(Constants::CCSC, const Level::Level &, const std::ostringstream &s) override {
        return s.str();
    }
};

/** Verify our set style was indeed set */
void style_access() {
    Style::set<Plain>();
    UNITTEST_ASSERT(dynamic_cast<Plain *>(Style::get().get()) != nullptr)
}

// Define the test
DEFINE_TEST(style_access)
