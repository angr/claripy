/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"
#include "utils.hpp"

#include <iostream>


using namespace Utils::Log;
using namespace UnitTest::TestLib;


/** Create a backend class */
struct Cout final : Backend::OStream {
    Cout() : Backend::OStream(std::make_shared<std::ostream>(std::cout.rdbuf()), true, false) {}
};

/** Verify our set backend was indeed set */
void backend_access() {
    Backend::set<Cout>();
    UNITTEST_ASSERT(Backend::get())
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backend_access)
