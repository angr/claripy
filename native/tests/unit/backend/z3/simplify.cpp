/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Try to simplify a claricpp expression via z3 */
void simplify() {
    auto z3 { Backend::Z3::Z3 {} };
    namespace Ex = Expression;

    // Test function
    const auto test = [&z3](const Ex::BasePtr &t, const Ex::BasePtr &sol) {
        return Ex::inline_repr(z3.simplify(t.get())) == Ex::inline_repr(sol);
    };

    // FP
    const auto fp_x { Create::literal(3.) };
    const auto fp_statement { Create::FP::add(fp_x, fp_x, Mode::FP::Rounding::TowardsZero) };
    UNITTEST_ASSERT(test(fp_statement, fp_statement)); // FP does not simplify

    // BV
    const auto bv_x { Create::literal(uint64_t { 3 }) };
    const auto bv_statement { Create::add({ bv_x, bv_x }) };
    const auto bv_sol { Create::literal(uint64_t { 6 }) };
    UNITTEST_ASSERT(test(bv_statement, bv_sol));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(simplify)
