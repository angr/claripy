/**
 * @file
 * \ingroup unittest
 */
#include "test_each_level.hpp"
#include "testlib.hpp"
#include "utils.hpp"

#include <iostream>
#include <memory>
#include <ostream>
#include <sstream>
#include <vector>


// For brevity
using namespace Utils::Log;
using namespace Backend;
using Lvl = Level::Level;
using namespace UnitTest::TestLib;


/** Test the given logging function */
void test(std::vector<std::shared_ptr<std::ostringstream>> &v, Lvl l) {
    if (Level::enabled(l)) {
        UNITTEST_ASSERT(v.size() == 2)
        for (auto &s : v) {
            const auto str { s->str() };
            UNITTEST_ASSERT(!str.empty())
            UNITTEST_ASSERT(str.back() == '\n')
            s->str(""); // clear the log for the next test
        }
    }
}

/** Test the multiplex backend */
void multiplex() {

    // The streams to be logged to
    std::vector<std::shared_ptr<std::ostringstream>> s;
    s.emplace_back(std::make_shared<std::ostringstream>());
    s.emplace_back(std::make_shared<std::ostringstream>());

    // Up cast
    auto ptr1 { Utils::Cast::Static::up<std::ostream>(s[0]) };
    auto ptr2 { Utils::Cast::Static::up<std::ostream>(s[1]) };

    // Create the real backend
    Multiplex multi;

    // Install the backends
    multi.backends.emplace_back(std::make_shared<OStream>(ptr1, true));
    multi.backends.emplace_back(std::make_shared<OStream>(ptr2, true));

    // Install the multi backend
    copy<Multiplex>(multi);

    // Test each level
    UnitTest::test_each_level(s, test, "");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(multiplex)
