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

    // For each op

    const auto op { Create::if_(Create::literal(true), Create::literal(4_ui),
                                Create::symbol<Expr::BV>("s", 64))
                        ->op };
    test_op(op);
    // @ todo
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(args)
