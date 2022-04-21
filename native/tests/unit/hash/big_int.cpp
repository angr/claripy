/**
 * @file
 * \ingroup unittest
 */
#include <set>
#include <testlib/testlib.hpp>


/** Verify that BigInts hash properly */
void big_int() {

    // For Brevity
    using M = boost::multiprecision::mpz_int;
    using L = U64;

    // Different L's
    const L l1 { 0x100000 };
    const L l2 { 0x200000 };

    // Different M's
    const M m1 { 1 };
    const M m2 { 0x100000000 };
    const M m3 { std::string(20, '9') + '8' };
    const M m4 { std::string(20, '9') + '9' };
    const M m5 { std::string(120, '9') };

    // Check if two literals contructed from BigInts constructed from the params are the same
    auto check_same = [&](const M &a1, const L a2, const M &b1, const L b2) {
        return Create::literal(BigInt { a1, a2 }) == Create::literal(BigInt { b1, b2 });
    };

    // Basic same
    bool same = check_same(m1, l1, m1, l1);
    UNITTEST_ASSERT(same);
    same = check_same(m1, l2, m1, l2);
    UNITTEST_ASSERT(same);
    same = check_same(m2, l2, m2, l2);
    UNITTEST_ASSERT(same);
    same = check_same(m3, l2, m3, l2);
    UNITTEST_ASSERT(same);
    same = check_same(m4, l2, m4, l2);
    UNITTEST_ASSERT(same);
    same = check_same(m5, l2, m5, l2);
    UNITTEST_ASSERT(same);
    same = check_same(m5, l1, m5, l1);
    UNITTEST_ASSERT(same);

    // Basic diff len
    same = check_same(m1, l1, m1, l2);
    UNITTEST_ASSERT(not same);
    same = check_same(m1, l2, m1, l1);
    UNITTEST_ASSERT(not same);
    same = check_same(m2, l2, m2, l1);
    UNITTEST_ASSERT(not same);
    same = check_same(m3, l2, m3, l1);
    UNITTEST_ASSERT(not same);
    same = check_same(m4, l2, m4, l1);
    UNITTEST_ASSERT(not same);
    same = check_same(m5, l2, m5, l1);
    UNITTEST_ASSERT(not same);
    same = check_same(m5, l1, m5, l2);
    UNITTEST_ASSERT(not same);

    // Basic diff size
    same = check_same(m1, l1, m2, l1);
    UNITTEST_ASSERT(not same);
    same = check_same(m1, l2, m2, l2);
    UNITTEST_ASSERT(not same);
    same = check_same(m2, l2, m3, l2);
    UNITTEST_ASSERT(not same);
    same = check_same(m3, l2, m4, l2);
    UNITTEST_ASSERT(not same);
    same = check_same(m4, l2, m5, l2);
    UNITTEST_ASSERT(not same);
    same = check_same(m5, l2, m1, l2);
    UNITTEST_ASSERT(not same);
    same = check_same(m4, l1, m5, l1);
    UNITTEST_ASSERT(not same);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(big_int)
