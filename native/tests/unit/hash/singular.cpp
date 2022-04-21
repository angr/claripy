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


/** Verify that hash singulars work */
void singular() {

    // Hashed
    auto s1 = std::make_shared<const TestHashed>(0_ui);
    auto s2 = std::make_shared<const TestHashed>(0_ui);
    auto s3 = std::make_shared<const TestHashed>(1_ui);
    UNITTEST_ASSERT(Hash::singular(s1) == Hash::singular(s2));
    UNITTEST_ASSERT(Hash::singular(s1) != Hash::singular(s3));

    // Constexpr compilation tests
    constexpr CCSC msg { "Hello" };
    constexpr auto c = Hash::singular(msg);
    constexpr auto cui = Hash::singular(0_ui);
    constexpr auto ci = Hash::singular(0_i);
    Util::sink(c, cui, ci);

    // Non-constexpr compilation tests
    (void) Hash::singular(std::vector<I64> { 0_i, 1_i });
    const std::string sref { "Hello" };
    (void) Hash::singular(sref);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(singular)
