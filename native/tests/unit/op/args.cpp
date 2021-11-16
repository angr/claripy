/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <algorithm>


/** Verify the two arg getter functions of o do not contradict */
static void test_op(const Op::BasePtr &op) {
    Op::Stack stack;
    std::vector<Op::ArgVar> args;

    // Call functions
    op->unsafe_add_reversed_children(stack);
    op->python_children(args);

    // Filter args
    std::vector<Expr::RawPtr> filtered {};
    for (const auto &i : args) {
        try {
            filtered.emplace_back(std::get<Expr::BasePtr>(i).get());
        }
        catch (std::bad_variant_access &) {
        }
    }

    // Compare
    UNITTEST_ASSERT(stack.size() == filtered.size());
    for (const auto &i : filtered) {
        const auto &top { stack.top() };
        UNITTEST_ASSERT(top == i);
        stack.pop();
    }
}

/** Verify that the two arg getter functions do not contradict each other */
void args() {
    namespace C = Create;

    // Constants
    const auto true_ { C::literal(true) };
    const auto bv_sym { C::symbol<Expr::BV>("bv_sym", 64) };

    // Functions
    const auto u64 { [](const UInt i) { return C::literal(i); } };
    const auto test { [](Expr::BasePtr e) { return test_op(e->op); } }; // NOLINT (copy is ok)

    // Non-trivial
    test(u64(4));
    test(bv_sym);
    test(C::if_(true_, u64(4), bv_sym));
    test(C::extract(1, 0, bv_sym));

    // @ todo
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(args)
