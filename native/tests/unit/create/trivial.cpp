/**
 * @file
 * \ingroup unittest
 */
#include "binary.hpp"
#include "flat.hpp"
#include "uint_binary.hpp"
#include "unary.hpp"


/** Test the trivial create functions */
void trivial() {
    namespace Log = Util::Log;
    namespace Cr = Create;

    /********************************************************************/
    /*                              Unary                               */
    /********************************************************************/

    Log::debug("Testing abs...");
    unary<Expr::FP, Op::Abs, Cr::abs>();

    Log::debug("Testing neg...");
    unary<Expr::BV, Op::Neg, Cr::neg>();
    unary<Expr::FP, Op::Neg, Cr::neg>();

    Log::debug("Testing not...");
    unary<Expr::Bool, Op::Not, Cr::not_>();

    Log::debug("Testing invert...");
    unary<Expr::BV, Op::Invert, Cr::invert>();

    Log::debug("Testing reverse...");
    unary<Expr::BV, Op::Reverse, Cr::reverse>();

    /********************************************************************/
    /*                            I64 Binary                            */
    /********************************************************************/

    Log::debug("Testing sign_ext...");
    uint_binary<Expr::BV, Op::SignExt, SM::Add, Cr::sign_ext>();

    Log::debug("Testing zero_ext...");
    uint_binary<Expr::BV, Op::ZeroExt, SM::Add, Cr::zero_ext>();

    /********************************************************************/
    /*                              Binary                              */
    /********************************************************************/

    // Comparisons

    Log::debug("Testing eq...");
    binary<Expr::Bool, Expr::FP, Op::Eq, SM::First, Cr::eq>();
    binary<Expr::Bool, Expr::BV, Op::Eq, SM::First, Cr::eq>();
    binary<Expr::Bool, Expr::Bool, Op::Eq, SM::First, Cr::eq>();
    binary<Expr::Bool, Expr::String, Op::Eq, SM::First, Cr::eq>();

/** A local macro used to test a comparison function */
#define TEST_COMPARE(T_, MASK)                                                                     \
    binary<Expr::Bool, T_, Op::Compare<MASK>, SM::First, Cr::compare<MASK>>();

/** A local macro used for brevity */
#define TEST_COMPARE_DUO(MASK)                                                                     \
    TEST_COMPARE(Expr::FP, Mode::Compare::MASK);                                                   \
    TEST_COMPARE(Expr::BV, Mode::Compare::MASK);

    Log::debug("Testing compare...");
    TEST_COMPARE(Expr::BV, Mode::Compare::UGE); // BV can be either
    TEST_COMPARE(Expr::BV, Mode::Compare::UGT);
    TEST_COMPARE(Expr::BV, Mode::Compare::ULE);
    TEST_COMPARE(Expr::BV, Mode::Compare::ULT);
    TEST_COMPARE_DUO(SGE); // FP comparisons must be signed
    TEST_COMPARE_DUO(SGT);
    TEST_COMPARE_DUO(SLE);
    TEST_COMPARE_DUO(SLT);

// Cleanup
#undef TEST_COMPARE
#undef TEST_COMPARE_MULTI

    // Math

    Log::debug("Testing sub...");
    binary<Expr::BV, Op::Sub, SM::First, Cr::sub>();

    Log::debug("Testing div...");
    using Sngd = Mode::Signed;
    binary<Expr::BV, Op::Div<Sngd::Signed>, SM::First, Cr::div<Sngd::Signed>>();
    binary<Expr::BV, Op::Div<Sngd::Unsigned>, SM::First, Cr::div<Sngd::Unsigned>>();

    Log::debug("Testing mod...");
    binary<Expr::BV, Op::Mod<Sngd::Signed>, SM::First, Cr::mod<Sngd::Signed>>();
    binary<Expr::BV, Op::Mod<Sngd::Unsigned>, SM::First, Cr::mod<Sngd::Unsigned>>();

    // Bitwise

/** A local macro used for testing a shift function */
#define TEST_SHIFT(MASK) binary<Expr::BV, Op::Shift<MASK>, SM::First, Cr::shift<MASK>>();

    Log::debug("Testing shift...");
    {
        using S = Mode::Shift;
        TEST_SHIFT(S::Left);
        TEST_SHIFT(S::ArithmeticRight);
        TEST_SHIFT(S::LogicalRight);
    }

// Cleanup
#undef TEST_SHIFT

    Log::debug("Testing rotate...");
    binary<Expr::BV, Op::Rotate<Mode::LR::Left>, SM::First, Cr::rotate<Mode::LR::Left>>();
    binary<Expr::BV, Op::Rotate<Mode::LR::Right>, SM::First, Cr::rotate<Mode::LR::Right>>();

    // Misc

    Log::debug("Testing widen...");
    binary<Expr::BV, Op::Widen, SM::First, Cr::widen>();

    Log::debug("Testing union...");
    binary<Expr::BV, Op::Union, SM::First, Cr::union_>();

    Log::debug("Testing intersection...");
    binary<Expr::BV, Op::Intersection, SM::First, Cr::intersection_>();
    binary<Expr::Bool, Op::Intersection, SM::First, Cr::intersection_>();

    Log::debug("Testing concat...");
    binary<Expr::BV, Op::Concat, SM::Add, Cr::concat>();
    binary<Expr::String, Op::Concat, SM::Add, Cr::concat>();

    /********************************************************************/
    /*                               Flat                               */
    /********************************************************************/

    // Math

    Log::debug("Testing add...");
    flat<Expr::BV, Op::Add, SM::First, Cr::add>();

    Log::debug("Testing mul...");
    flat<Expr::BV, Op::Mul, SM::First, Cr::mul>();

    // Logical

    Log::debug("Testing or...");
    flat<Expr::BV, Op::Or, SM::First, Cr::or_>();
    flat<Expr::Bool, Op::Or, SM::First, Cr::or_>();

    Log::debug("Testing and...");
    flat<Expr::BV, Op::And, SM::First, Cr::and_>();
    flat<Expr::Bool, Op::And, SM::First, Cr::and_>();

    Log::debug("Testing xor...");
    flat<Expr::BV, Op::Xor, SM::First, Cr::xor_>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
