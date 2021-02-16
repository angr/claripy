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

    binary<Expression::BV, Op::Or, SM::First, Create::or_<Expression::BV>>();
    binary<Expression::Bool, Op::Or, SM::First, Create::or_<Expression::Bool>>();

    binary<Expression::BV, Op::And, SM::First, Create::and_<Expression::BV>>();
    binary<Expression::Bool, Op::And, SM::First, Create::and_<Expression::Bool>>();

    binary<Expression::BV, Op::Xor, SM::First, Create::xor_>();

    binary<Expression::BV, Op::Pow, SM::First, Create::pow>();

    binary<Expression::BV, Op::Mod, SM::First, Create::mod>();

    binary<Expression::BV, Op::DivMod, SM::First, Create::div_mod>();

    // Flat

    flat<Expression::BV, Op::Add, SM::First, Create::add>();

    flat<Expression::BV, Op::Mul, SM::First, Create::mul>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
