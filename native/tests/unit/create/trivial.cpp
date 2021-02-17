/**
 * @file
 * \ingroup unittest
 */
#include "binary.hpp"
#include "flat.hpp"
#include "unary.hpp"


/** Test the trivial create functions */
void trivial() {
    namespace Log = Utils::Log;
    namespace Ex = Expression;
    namespace Cr = Create;

    /********************************************************************/
    /*                              Unary                               */
    /********************************************************************/

    Log::debug("Testing abs...");
    unary<Ex::BV, Op::Abs, Cr::abs<Expression::BV>>();

    Log::debug("Testing neg...");
    unary<Ex::BV, Op::Neg, Cr::neg<Expression::BV>>();

    Log::debug("Testing invert...");
    unary<Ex::BV, Op::Invert, Cr::invert<Expression::BV>>();
    unary<Ex::Bool, Op::Invert, Cr::invert<Expression::Bool>>();

    Log::debug("Testing reverse...");
    unary<Ex::BV, Op::Reverse, Cr::reverse>();

    /********************************************************************/
    /*                              Binary                              */
    /********************************************************************/

    // Comparisons

    Log::debug("Testing reverse...");
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

    Log::debug("Testing compare...");
    TEST_COMPARE_2(Ex::FP, true) // FP comparisons must be signed
    TEST_COMPARE_2(Ex::BV, true) // BV can be either
    TEST_COMPARE_2(Ex::BV, false)

// Cleanup
#undef TEST_COMPARE
#undef TEST_COMPARE_1
#undef TEST_COMPARE_2

    // Math

    Log::debug("Testing sub...");
    binary<Ex::BV, Op::Sub, SM::First, Cr::sub>();

    Log::debug("Testing div...");
    binary<Ex::BV, Op::Div, SM::First, Cr::div>();

    Log::debug("Testing pow...");
    binary<Ex::BV, Op::Pow, SM::First, Cr::pow>();

    Log::debug("Testing mod...");
    binary<Ex::BV, Op::Mod, SM::First, Cr::mod>();

    Log::debug("Testing div_mod...");
    binary<Ex::BV, Op::DivMod, SM::First, Cr::div_mod>();

    // Bitwise

    Log::debug("Testing shift...");
    binary<Ex::BV, Op::Shift<true>, SM::First, Cr::shift<true>>();
    binary<Ex::BV, Op::Shift<false>, SM::First, Cr::shift<false>>();

    Log::debug("Testing rotate...");
    binary<Ex::BV, Op::Rotate<true>, SM::First, Cr::rotate<true>>();
    binary<Ex::BV, Op::Rotate<false>, SM::First, Cr::rotate<false>>();

    // Logical

    Log::debug("Testing or...");
    binary<Ex::BV, Op::Or, SM::First, Cr::or_<Expression::BV>>();
    binary<Ex::Bool, Op::Or, SM::First, Cr::or_<Expression::Bool>>();

    Log::debug("Testing and...");
    binary<Ex::BV, Op::And, SM::First, Cr::and_<Expression::BV>>();
    binary<Ex::Bool, Op::And, SM::First, Cr::and_<Expression::Bool>>();

    Log::debug("Testing xor...");
    binary<Ex::BV, Op::Xor, SM::First, Cr::xor_>();

    // Misc

    Log::debug("Testing widen...");
    binary<Ex::BV, Op::Widen, SM::First, Cr::widen>();

    Log::debug("Testing union...");
    binary<Ex::BV, Op::Union, SM::First, Cr::union_>();

    Log::debug("Testing intersection...");
    binary<Ex::BV, Op::Intersection, SM::First, Cr::intersection_<Expression::BV>>();
    binary<Ex::Bool, Op::Intersection, SM::First, Cr::intersection_<Expression::Bool>>();

    Log::debug("Testing concat...");
    binary<Ex::BV, Op::Concat, SM::Add, Cr::concat<Expression::BV>>();

    /********************************************************************/
    /*                               Flat                               */
    /********************************************************************/

    Log::debug("Testing add...");
    flat<Ex::BV, Op::Add, SM::First, Cr::add>();

    Log::debug("Testing mul...");
    flat<Ex::BV, Op::Mul, SM::First, Cr::mul>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
