/**
 * @file
 * \ingroup unittest
 */
#include "shim_z3.hpp"

#include <testlib/testlib.hpp>

/** Test how the z3 backend handles sym_an_trans_data */
void sym_an_trans_data() {
    UnitTest::Friend::ShimZ3 z3;

    // Create a dict with an annotation
    using namespace pybind11::literals;
    pybind11::str hi { "hello" };
    pybind11::tuple tup { 1 };
    tup[0] = hi;
    pybind11::dict d { ANNOTATIONS_KEY ""_a = tup };

    // Create an BV symbol
    const auto sym { Create::symbol<Expr::BV>(std::string { "x" }, std::move(d), 32_ui) };

    // Round trip it through z3
    const auto conv { z3.convert(sym.get()) };
    const auto abs { z3.abstract(conv) };

    // Tests
    UNITTEST_ASSERT(sym == abs);
    UNITTEST_ASSERT(sym->annotations() == abs->annotations());

    // Sanity check that nothing changed / everything is as expected
    UNITTEST_ASSERT(hi.is(sym->annotations().value()[0]));

    // Verify data can be cleared
    z3.bk.clear_persistent_data();
    const auto abs2 { z3.abstract(conv) };
    UNITTEST_ASSERT(sym != abs2);
    UNITTEST_ASSERT(abs != abs2);
    UNITTEST_ASSERT(not abs2->annotations());
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sym_an_trans_data)
