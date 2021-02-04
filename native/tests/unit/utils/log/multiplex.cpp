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
    s.emplace_back(new std::ostringstream); // NOLINT
    s.emplace_back(new std::ostringstream); // NOLINT

    // Up cast
    auto ptr1 { Utils::up_cast<std::ostream>(s[0]) };
    auto ptr2 { Utils::up_cast<std::ostream>(s[1]) };

    // Create the real backend
    Multiplex multi;

    // Create the backends to be multiplex to
    Multiplex::BackendContainer c;
    c.emplace_back(new OStream { ptr1, true }); // NOLINT
    c.emplace_back(new OStream { ptr2, true }); // NOLINT

    // Install the backends
    multi.backends.set_copy<Multiplex::BackendContainer>(c);

    // Install the multi backend
    copy<Multiplex>(multi);

    // Test each level
    UnitTest::test_each_level(s, test, "");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(multiplex)
