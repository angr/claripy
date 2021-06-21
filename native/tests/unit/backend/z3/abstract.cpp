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

#if 0

	auto f = Create::literal(3425.f);
	auto c = z3.convert(f);
	(void) z3.abstract(c);

#else
    // Create a z3 expression
    const auto ite { make_ite("Hello") };
    const auto conv { z3.convert(ite.get()) };

    // Verify abstraction runs
    (void) z3.abstract(conv);
#endif
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abstract)
