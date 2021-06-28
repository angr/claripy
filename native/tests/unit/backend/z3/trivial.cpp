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
    for (const auto &func : functions) {
        func();
    }
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)


/**********************************************************/
/*                  General Expressions                   */
/**********************************************************/


Backend::Z3::Z3 z3bk;

const auto fp_x { Create::symbol<Ex::FP>("fp_x", 64_ui) };
const auto bv_x { Create::symbol<Ex::BV>("bv_x", 64_ui) };
const auto bool_x { Create::symbol("bool_x") };


/**********************************************************/
/*                   Trivial Functions                    */
/**********************************************************/


bool test_id(const Expression::BasePtr &&x) {
    return z3bk.abstract(z3bk.convert(x)) == x;
}

ADD_TEST(abs) {
    UNITTEST_ASSERT(test_id(Create::abs(fp_x)));
}

ADD_TEST(neg) {
    UNITTEST_ASSERT(test_id(Create::neg<Ex::FP>(fp_x)));
    UNITTEST_ASSERT(test_id(Create::neg<Ex::BV>(bv_x)));
}


ADD_TEST(not_) {
    UNITTEST_ASSERT(test_id(Create::not_(bool_x)));
}

ADD_TEST(invert) {
    UNITTEST_ASSERT(test_id(Create::invert(bv_x)));
}

/* ADD_TEST(reverse) { */
/*     UNITTEST_ASSERT(test_id(Create::reverse(bv_x))); */
/* } */
