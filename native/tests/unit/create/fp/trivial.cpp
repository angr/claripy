/**
 * @file
 * \ingroup unittest
 */
#include "mode_binary.hpp"

#include "../binary.hpp"
#include "../ternary.hpp"
#include "../unary.hpp"


/** Test the trivial create fp functions */
void trivial() {

    // Unary

    Util::Log::debug("Testing Fp::IsNan...");
    unary<Expr::Bool, Expr::FP, Op::FP::IsNan, Create::FP::is_nan>();

    Util::Log::debug("Testing Fp::ToIEEEBV...");
    unary<Expr::BV, Expr::FP, Op::FP::ToIEEEBV, Create::FP::to_ieee_bv>();

    // ModeBinary

    Util::Log::debug("Testing Fp::Add...");
    mode_binary<Op::FP::Add, Create::FP::add>();

    Util::Log::debug("Testing Fp::Sub...");
    mode_binary<Op::FP::Sub, Create::FP::sub>();

    Util::Log::debug("Testing Fp::Div...");
    mode_binary<Op::FP::Div, Create::FP::div>();

    // Ternary

    Util::Log::debug("Testing Fp::FP...");
    ternary<Expr::FP, Expr::BV, Op::FP::FP, SM::Add, Create::FP::fp>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
