/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


using namespace Util::Log;
using namespace UnitTest::TestLib;


/** Create a style class */
struct Plain final : Style::Base {
    /** The style name */
    [[nodiscard]] inline const char *name() const noexcept final { return "Plain"; }
    /** The style function */
    inline std::string str(CCSC, const Level::Lvl, std::string &&s) const final {
        return std::move(s);
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
