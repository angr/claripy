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

#define M_TEST_COMPARE(T_, OPT)                                                                    \
    binary<Expr::Bool, T_, Op::OPT, SM::First, Cr::inequality<Op::OPT>>();

#define M_TEST_COMPARE_DUO(OPT)                                                                    \
    M_TEST_COMPARE(Expr::FP, OPT);                                                                 \
    M_TEST_COMPARE(Expr::BV, OPT);

    Log::debug("Testing compare...");
    M_TEST_COMPARE_DUO(SGE);
    M_TEST_COMPARE_DUO(SGT);
    M_TEST_COMPARE_DUO(SLE);
    M_TEST_COMPARE_DUO(SLT);
    // BV can be unsigned
    M_TEST_COMPARE(Expr::BV, UGE);
    M_TEST_COMPARE(Expr::BV, UGT);
    M_TEST_COMPARE(Expr::BV, ULE);
    M_TEST_COMPARE(Expr::BV, ULT);
#undef M_TEST_COMPARE
#undef M_TEST_COMPARE_MULTI

    // Math

    Log::debug("Testing sub...");
    binary<Expr::BV, Op::Sub, SM::First, Cr::sub>();

    Log::debug("Testing div...");
    binary<Expr::BV, Op::DivSigned, SM::First, Cr::div_signed>();
    binary<Expr::BV, Op::DivUnsigned, SM::First, Cr::div_unsigned>();

    Log::debug("Testing mod...");
    binary<Expr::BV, Op::ModSigned, SM::First, Cr::mod_signed>();
    binary<Expr::BV, Op::ModUnsigned, SM::First, Cr::mod_unsigned>();

    // Bitwise

    Log::debug("Testing shift...");
    {
#define M_TEST_SHIFT(OPT) binary<Expr::BV, OPT, SM::First, Cr::shift<OPT>>();
        M_TEST_SHIFT(Op::ShiftArithmeticRight);
        M_TEST_SHIFT(Op::ShiftLogicalRight);
        M_TEST_SHIFT(Op::ShiftLeft);
#undef M_TEST_SHIFT
    }

    Log::debug("Testing rotate...");
    binary<Expr::BV, Op::RotateLeft, SM::First, Cr::rotate_left>();
    binary<Expr::BV, Op::RotateRight, SM::First, Cr::rotate_right>();

    // Misc

    Log::debug("Testing widen...");
    binary<Expr::BV, Op::Widen, SM::First, Cr::widen>();

    Log::debug("Testing union...");
    binary<Expr::BV, Op::Union, SM::First, Cr::union_>();

    Log::debug("Testing intersection...");
    binary<Expr::BV, Op::Intersection, SM::First, Cr::intersection_>();
    binary<Expr::Bool, Op::Intersection, SM::First, Cr::intersection_>();

    /********************************************************************/
    /*                               Flat                               */
    /********************************************************************/

    Log::debug("Testing concat...");
    flat<Expr::BV, Op::Concat, SM::Add, Cr::concat>();
    flat<Expr::String, Op::Concat, SM::Add, Cr::concat>();

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
