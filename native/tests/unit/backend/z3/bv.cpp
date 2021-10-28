/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Test a BV created from x */
template <typename B, typename T> static void test_bv_ctor(B &z3, T x) {
    const auto lit { Create::literal(std::move(x)) };
    const auto simp { z3.simplify(lit.get()) }; // Not erroring here is the main test
    UNITTEST_ASSERT(lit == simp);
}

/** Test is_true and is_false */
void bv() {
    Backend::Z3::Z3 z3;
    z3.big_int_mode(Mode::BigInt::Int);

    // Constants
    const boost::multiprecision::mpz_int big_one { 1 };            // NOLINT
    const auto l1 { Create::literal(BigInt { big_one, 200_ui }) }; // NOLINT
    const auto l2 { Create::literal(BigInt { big_one, 100_ui }) }; // NOLINT

    // Constructors
    Util::Log::debug("Testing BV constructor via uint8");
    test_bv_ctor(z3, uint8_t { 3 });
    Util::Log::debug("Testing BV constructor via uint16");
    test_bv_ctor(z3, uint16_t { 3 });
    Util::Log::debug("Testing BV constructor via uint32");
    test_bv_ctor(z3, uint32_t { 3 });
    Util::Log::debug("Testing BV constructor via uint64");
    test_bv_ctor(z3, uint64_t { 3 });
    Util::Log::debug("Testing BV constructor via BigInt with mode Int");
    test_bv_ctor(z3, BigInt { big_one, 300_ui }); // NOLINT

    // BigInt abstraction mode
    const auto old { z3.big_int_mode(Mode::BigInt::Str) };
    Util::Log::debug("Testing BV constructor via BigInt with mode Str");
    test_bv_ctor(z3, BigInt { big_one.str(), 300_ui }); // NOLINT
    (void) z3.big_int_mode(old);                        // Reset

    // Sizes same
    Util::Log::debug("Testing x/x");
    const auto one_same { Create::div<false>(l1, l1) };
    UNITTEST_ASSERT(l1 == z3.simplify(one_same.get()));

    // Sizes differ
    Util::Log::debug("Testing x/x with different sized x's; this *should* error");
    try {
        const auto fail { Create::div<false>(l1, l2) };
        UNITTEST_ERR("It should not be possible to construct this: ", fail);
    }
    catch (Error::Expr::Type &) {
        Util::Log::info("Desired error detected: success.");
    }
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(bv)
