/**
 * @file
 * \ingroup unittest
 */
#include <set>
#include <testlib/testlib.hpp>


/** A hashed struct */
struct TestHashed : public Hash::Hashed {
    CUID_DEFINE_MAYBE_UNUSED;
    /** Constructor */
    explicit TestHashed(const Hash::Hash h) noexcept : Hashed { h } {}
};


/** Verify that hashing of multiple objects works */
void hash() {
    std::set<Hash::Hash> hashes;

    // Values to use
    using PT = std::shared_ptr<const TestHashed>;
    const PT a0 { std::make_shared<const TestHashed>(0_ui) };
    const PT a1 { std::make_shared<const TestHashed>(1_ui) };
    const std::string hi_s { "hi" };
    const CCSC hi_c { "hi" };
    const std::vector<PT> vec1 { PT { a0 }, PT { a1 } };
    const std::vector<PT> vec2 { PT { a1 }, PT { a0 } };
    const U64 uz { 0_ui };
    const I64 z { 0_i };

    // Hash multiple things

    hashes.insert(Hash::hash(a0, hi_s, z)); // 1
    hashes.insert(Hash::hash(a0, hi_s, z)); // 1

    hashes.insert(Hash::hash(a0, hi_s, uz)); // 2

    hashes.insert(Hash::hash(vec1)); // 3

    hashes.insert(Hash::hash(vec2)); // 4

    hashes.insert(Hash::hash(hi_s, hi_c)); // 5
    hashes.insert(Hash::hash(hi_s, hi_c)); // 5

    hashes.insert(Hash::hash(hi_c, hi_s)); // 6
    hashes.insert(Hash::hash(hi_c, hi_s)); // 6

    hashes.insert(Hash::hash(a0)); // 7

    hashes.insert(Hash::hash(a1)); // 8

    // Verify uniqueness
    UNITTEST_ASSERT(hashes.size() == 8);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(hash)
