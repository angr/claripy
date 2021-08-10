/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Test a BV created from x */
template <typename T> static void test_bv(T x) {
    auto z3 { Backend::Z3::Z3 {} };
    const auto lit { Create::literal(std::move(x)) };
    const auto simp { z3.simplify(lit) }; // Not erroring here is the main test
    UNITTEST_ASSERT(lit == simp);
}

/** Test is_true and is_false */
void bv() {
    Utils::Log::Debug("Testing BV via uint8");
    test_bv(uint8_t { 3 });
    Utils::Log::Debug("Testing BV via uint16");
    test_bv(uint16_t { 3 });
    Utils::Log::Debug("Testing BV via uint32");
    test_bv(uint32_t { 3 });
    Utils::Log::Debug("Testing BV via uint64");
    test_bv(uint64_t { 3 });
    Utils::Log::Debug("Testing BV via BigInt");
    const boost::multiprecision::mpz_int big { 4 }; // NOLINT
    test_bv(BigInt { big, 200_ui });                // NOLINT
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(bv)