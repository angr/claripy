/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


using namespace Util::Log;
using namespace UnitTest::TestLib;


/** Create a style class */
struct Plain final : Style::Base {
    /** The style function */
    std::string str(CCSC, const Level::Level &, const std::ostringstream &s) const override final {
        return s.str();
    }
};

/** Verify our set style was indeed set */
void style_access() {
    Style::set<Plain>();
    const bool success { dynamic_cast<const Plain *>(Style::get().get()) != nullptr };
    UNITTEST_ASSERT(success);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(style_access)
