/**
 * @file
 * \ingroup unittest
 */
#include <iostream>
#include <testlib/testlib.hpp>


namespace L = Util::Log;
using namespace UnitTest::TestLib;


/** Create a backend class */
struct Cout final : L::Backend::OStream {
    Cout() : OStream(std::make_shared<std::ostream>(std::cout.rdbuf()), true, false) {}
};

/** Verify our set backend was indeed set */
void backend_access() {
    L::Backend::set<Cout>();
    const bool success { dynamic_cast<const Cout *>(L::Backend::get().get()) != nullptr };
    UNITTEST_ASSERT(success);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backend_access)
