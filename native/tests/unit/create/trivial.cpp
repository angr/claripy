/**
 * @file
 * \ingroup unittest
 */
#include "binary.hpp"
#include "flat.hpp"
#include "unary.hpp"


/** Test the trivial create functions */
void trivial() {
    namespace Ex = Expression;
    namespace Cr = Create;

    /********************************************************************/
    /*                              Unary                               */
    /********************************************************************/

    unary<Ex::BV, Op::Abs, Cr::abs<Expression::BV>>();

    unary<Ex::BV, Op::Neg, Cr::neg<Expression::BV>>();

    unary<Ex::BV, Op::Invert, Cr::invert<Expression::BV>>();
    unary<Ex::Bool, Op::Invert, Cr::invert<Expression::Bool>>();

    unary<Ex::BV, Op::Reverse, Cr::reverse>();

    /********************************************************************/
    /*                              Binary                              */
    /********************************************************************/

    // Comparisons

    binary<Ex::Bool, Op::Eq, SM::First, Cr::eq<Expression::Bool>>();

/** A macro used to test a comparison function */
#define TEST_COMPARE(T_, S_, L_, E_)                                                              \
    binary<Ex::Bool, T_, Op::Compare<S_, L_, E_>, SM::First, Cr::compare<T_, S_, L_, E_>>();

/** A macro used to test a comparison function for all values of Equals */
#define TEST_COMPARE_1(T_, S_, L_)                                                                \
    TEST_COMPARE(T_, S_, L_, true)                                                                \
    TEST_COMPARE(T_, S_, L_, false)

/** A macro used to test a comparison function for all values of Less and Equals */
#define TEST_COMPARE_2(T_, S_)                                                                    \
    TEST_COMPARE_1(T_, S_, true)                                                                  \
    TEST_COMPARE_1(T_, S_, false)

    TEST_COMPARE_2(Ex::FP, true) // FP comparisons must be signed
    TEST_COMPARE_2(Ex::BV, true) // BV can be either
    TEST_COMPARE_2(Ex::BV, false)

// Cleanup
#undef TEST_COMPARE
#undef TEST_COMPARE_1
#undef TEST_COMPARE_2

    // Math

    binary<Ex::BV, Op::Sub, SM::First, Cr::sub>();

    binary<Ex::BV, Op::Div, SM::First, Cr::div>();

    binary<Ex::BV, Op::Pow, SM::First, Cr::pow>();

    binary<Ex::BV, Op::Mod, SM::First, Cr::mod>();

    binary<Ex::BV, Op::DivMod, SM::First, Cr::div_mod>();

    // Logical

    binary<Ex::BV, Op::Or, SM::First, Cr::or_<Expression::BV>>();
    binary<Ex::Bool, Op::Or, SM::First, Cr::or_<Expression::Bool>>();

    binary<Ex::BV, Op::And, SM::First, Cr::and_<Expression::BV>>();
    binary<Ex::Bool, Op::And, SM::First, Cr::and_<Expression::Bool>>();

    binary<Ex::BV, Op::Xor, SM::First, Cr::xor_>();

    // Misc

    binary<Ex::BV, Op::Concat, SM::Add, Cr::concat<Expression::BV>>();

    /********************************************************************/
    /*                               Flat                               */
    /********************************************************************/

    flat<Ex::BV, Op::Add, SM::First, Cr::add>();

    flat<Ex::BV, Op::Mul, SM::First, Cr::mul>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
