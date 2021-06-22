/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

#include "../../make_ite.hpp"


/** Try to abstract a claricpp expression from z3 */
void abstract() {
    auto z3 { Backend::Z3::Z3 {} };

    // Create a z3 expression
    /* const auto ite { make_ite("Hello") }; */
    const auto ite { Create::literal(std::string { "Hello" }) };
    const auto conv { z3.convert(ite.get()) };

    // Verify abstraction runs
    (void) z3.abstract(conv);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abstract)
