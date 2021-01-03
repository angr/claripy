/** @file */

#include "test_each_level.hpp"
#include "testlib.hpp"
#include "utils.hpp"

#include <iostream>
#include <memory>
#include <ostream>
#include <sstream>
#include <vector>

using namespace Utils::Log;
using namespace Backend;
using Lvl = Level::Level;
using namespace UnitTest::TestLib;

namespace UnitTest {
    /** Allow accessing of OStream's private stream */
    struct ClaricppUnitTest {
        /** Extraction function */
        static std::ostream &extract(OStream *o) { return o->stream; }
    };
} // namespace UnitTest

/** Test the given logging function */
void test(std::vector<std::ostringstream> &s, Lvl l) {
    if (UTILS_LOG_LEVEL_IMPLIES(Level::get(), l)) {
        UNITTEST_ASSERT(s.size() == 2)
        for (unsigned i = 0; i < s.size(); ++i) {
            const auto str = s[i].str();
            UNITTEST_ASSERT(str.size() > 0)
            UNITTEST_ASSERT(str.back() == '\n')
            s[i].str(""); // clear the log for the next test
        }
    }
}

/** Test the multiplex backend */
int multiplex() {

    // The streams to be logged to
    std::vector<std::ostringstream> s(2);

    // Construct the first backend
    OStream *o1 = new OStream(s[0], true);
    std::shared_ptr<AbstractBase> ptr1(o1);
    Multiplex multi = { ptr1 };

    // Emplace the second backend
    const bool true_ = true;
    multi.emplace<OStream>(s[1], true_);

    // Install the multi backend
    copy<Multiplex>(multi);

    // Test each level
    UnitTest::test_each_level(s, test, "");
    return 0;
}
