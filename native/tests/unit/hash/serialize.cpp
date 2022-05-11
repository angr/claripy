/**
 * @file
 * \ingroup unittest
 */
#include <set>
#include <testlib/testlib.hpp>


/** A hashed struct */
struct TestHashed : public Hash::Hashed {
    /** Constructor */
    explicit TestHashed(const Hash::Hash h) noexcept : Hashed { h } {}
};


/** Verify that hash serializes work */
void serialize() {

    // Hashed
    auto s1 = std::make_shared<const TestHashed>(0_ui);
    auto s2 = std::make_shared<const TestHashed>(0_ui);
    auto s3 = std::make_shared<const TestHashed>(1_ui);
    UNITTEST_ASSERT(Hash::serialize(s1) == Hash::serialize(s2));
    UNITTEST_ASSERT(Hash::serialize(s1) != Hash::serialize(s3));

    // Constexpr compilation tests
    constexpr CCSC msg { "Hello" };
    constexpr auto c = Hash::serialize(msg);
    constexpr auto cui = Hash::serialize(0_ui);
    constexpr auto ci = Hash::serialize(0_i);
    Util::sink(c, cui, ci);

    // Non-constexpr compilation tests
    (void) Hash::serialize(std::vector<I64> { 0_i, 1_i });
    const std::string sref { "Hello" };
    (void) Hash::serialize(sref);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(serialize)
