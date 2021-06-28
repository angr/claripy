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


/**********************************************************/
/*                   Trivial Functions                    */
/**********************************************************/


ADD_TEST(abs) {
    const auto abs { Create::abs(fp_x) };
    Utils::Log::warning(__FILE__ " ", __LINE__);
    const auto simp { z3bk.simplify(abs) };
    UNITTEST_ASSERT(abs == simp);
}

template <typename T> void neg_test(const Expression::BasePtr &x) {
    const auto neg { Create::neg<T>(x) };
    Utils::Log::warning(__FILE__ " ", __LINE__);
    const auto test { z3bk.abstract(z3bk.convert(neg)) };
    UNITTEST_ASSERT(test == neg);
}

ADD_TEST(neg) {
    neg_test<Ex::FP>(fp_x);
    neg_test<Ex::BV>(bv_x);
}
