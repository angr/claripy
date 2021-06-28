/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

// For brevity
namespace Ex = Expression;


/** The type of test functions */
using Func = void (*)();

/** List of functions to test */
std::vector<Func> functions {};


/** A macro to define a new test function */
#define ADD_TEST(FNAME)                                                                           \
    void FNAME();                                                                                 \
    UTILS_RUN_STATEMENT_BEFORE_MAIN(functions.push_back(&FNAME));                                 \
    void FNAME()


/** Test trivial ops in claricpp */
void trivial() {

    Backend::Z3::Z3 z3bk;

    const auto fp_x { Create::symbol<Ex::FP>("fp_x", 64_ui) };
    const auto bv_x { Create::symbol<Ex::BV>("bv_x", 64_ui) };
    const auto bool_x { Create::symbol("bool_x") };

    // Verify the round trip changes nothing
    const auto test_id = [&z3bk](const Expression::BasePtr &&x) {
        return z3bk.abstract(z3bk.convert(x)) == x;
    };

    // Unary

    UNITTEST_ASSERT(test_id(Create::abs(fp_x)));
    UNITTEST_ASSERT(test_id(Create::not_(bool_x)));
    UNITTEST_ASSERT(test_id(Create::invert(bv_x)));

    // Neg
    UNITTEST_ASSERT(test_id(Create::neg<Ex::FP>(fp_x)));
    UNITTEST_ASSERT(test_id(Create::neg<Ex::BV>(bv_x)));

    // Reverse
    const auto also_x { Create::reverse(Create::reverse(bv_x)) };
    UNITTEST_ASSERT(z3bk.simplify(also_x) == bv_x);

    // UInt Binary

    /* UNITTEST_ASSERT(test_id(Create::sign_ext(bv_x, 1))); */
    /* UNITTEST_ASSERT(test_id(Create::zero_ext(bv_x, 1))); */
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
