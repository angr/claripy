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
void test(std::vector<std::shared_ptr<std::ostringstream>> &s, Lvl l) {
    if (Level::enabled(l)) {
        UNITTEST_ASSERT(s.size() == 2)
        for (unsigned i = 0; i < s.size(); ++i) {
            const auto str = s[i]->str();
            UNITTEST_ASSERT(!str.empty())
            UNITTEST_ASSERT(str.back() == '\n')
            s[i]->str(""); // clear the log for the next test
        }
    }
}

/** Test the multiplex backend */
void multiplex() {

    // The streams to be logged to
    std::vector<std::shared_ptr<std::ostringstream>> s;
    s.emplace_back(new std::ostringstream);
    s.emplace_back(new std::ostringstream);

    // Create the real backend
    Multiplex multi;

    // Create the backends to be multiplex to
    Multiplex::BackendContainer c;
    c.emplace_back(new OStream(std::static_pointer_cast<std::ostream>(s[0]), true));
    c.emplace_back(new OStream(std::static_pointer_cast<std::ostream>(s[1]), true));

    // Install the backends
    multi.backends.set_copy<Multiplex::BackendContainer>(c);

    // Install the multi backend
    copy<Multiplex>(multi);

    // Test each level
    UnitTest::test_each_level(s, test, "");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(multiplex)
