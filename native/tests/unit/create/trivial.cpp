/**
 * @file
 * \ingroup unittest
 */
#include "binary.hpp"
#include "flat.hpp"
#include "unary.hpp"


/** Test the trivial create functions */
void trivial() {

    // Unary

    unary<Expression::BV, Op::Abs, Create::abs<Expression::BV>>();

    unary<Expression::BV, Op::Neg, Create::neg<Expression::BV>>();

    unary<Expression::BV, Op::Invert, Create::invert<Expression::BV>>();
    unary<Expression::Bool, Op::Invert, Create::invert<Expression::Bool>>();

    unary<Expression::BV, Op::Reverse, Create::reverse>();

    // Binary

    binary<Expression::BV, Op::Concat, SM::Add, Create::concat<Expression::BV>>();

    binary<Expression::BV, Op::Sub, SM::First, Create::sub>();

    binary<Expression::BV, Op::Div, SM::First, Create::div>();

    binary<Expression::Bool, Op::Eq, SM::First, Create::eq<Expression::Bool>>();

    // Flat

    flat<Expression::BV, Op::Add, SM::First, Create::add>();

    flat<Expression::BV, Op::Mul, SM::First, Create::mul>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
