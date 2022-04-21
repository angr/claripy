/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


using namespace Util::Log;
using namespace UnitTest::TestLib;


/** Each construction should have a unique pointer */
void level_access() {

    // Get the current level
    const auto init { Level::get() };

#ifdef CONSTANT_LOG_LEVEL
    (void) init;
#else
    // Select a different level
    const auto different { (init == Level::info) ? Level::debug : Level::info };
    Level::set(different);

    // Error checking
    UNITTEST_ASSERT(Level::get() != init);
#endif
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(level_access)
