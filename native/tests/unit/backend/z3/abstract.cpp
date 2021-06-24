/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

#include "../../make_ite.hpp"


/** Try to abstract a claricpp expression from z3 */
void abstract() {

    z3::context ctx;
    auto b { ctx.string_val("Hello") };
    auto decl { b.decl() };
    auto decl_kind { decl.decl_kind() };
    Utils::Log::critical(b);
    Utils::Log::critical(decl);
    Utils::Log::critical(decl_kind);

#if 0
    auto z3 { Backend::Z3::Z3 {} };

    // Create a z3 expression
    /* const auto ite { make_ite("Hello") }; */
    const auto ite { Create::literal(std::string { "Hello" }) };
    const auto conv { z3.convert(ite.get()) };

    // Verify abstraction runs
    (void) z3.abstract(conv);
#endif
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abstract)
