/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Try to simplify a claricpp expr via z3 */
void simplify() {
    auto z3 { Backend::Z3::Z3 {} };

    // Test function
    const auto test = [&z3](const Expr::BasePtr &t, const Expr::BasePtr &sol) {
        return z3.simplify(t.get())->repr() == sol->repr();
    };

    // FP
    const auto fp_x { Create::literal(3.) };
    const auto fp_statement { Create::FP::add(fp_x, fp_x, Mode::FP::Rounding::TowardsZero) };
    UNITTEST_ASSERT(test(fp_statement, fp_statement)); // FP does not simplify

    // BV
    const auto bv_x { Create::literal(U64 { 3 }) };
    const auto bv_statement { Create::add({ bv_x, bv_x }) };
    const auto bv_sol { Create::literal(U64 { 6 }) };
    UNITTEST_ASSERT(test(bv_statement, bv_sol));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(simplify)
