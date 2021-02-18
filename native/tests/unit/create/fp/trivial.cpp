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
    namespace Log = Utils::Log;
    namespace Ex = ::Expression;

    // Unary

    Log::debug("Testing Fp::IsInf...");
    unary<Ex::Bool, Ex::FP, Op::FP::IsInf, SM::NA, Create::FP::is_inf>();

    Log::debug("Testing Fp::IsNaN...");
    unary<Ex::Bool, Ex::FP, Op::FP::IsNaN, SM::NA, Create::FP::is_nan>();

    Log::debug("Testing Fp::ToIEEEBV...");
    unary<Ex::BV, Ex::FP, Op::FP::ToIEEEBV, SM::First, Create::FP::to_ieee_bv>();

    // Binary

    Log::debug("Testing Fp::NE...");
    binary<Ex::Bool, Ex::FP, Op::FP::NE, SM::NA, Create::FP::ne>();

    // ModeBinary

    Log::debug("Testing Fp::Add...");
    mode_binary<Op::FP::Add, Create::FP::add>();

    Log::debug("Testing Fp::Sub...");
    mode_binary<Op::FP::Sub, Create::FP::sub>();

    Log::debug("Testing Fp::Div...");
    mode_binary<Op::FP::Div, Create::FP::div>();

    // Ternary

    Log::debug("Testing Fp::FP...");
    ternary<Ex::FP, Ex::BV, Op::FP::FP, SM::Add, Create::FP::fp>();
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(trivial)
