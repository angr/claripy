/**
 * @file
 * \ingroup unittest
 */
#include "hash.hpp"
#include "testlib.hpp"

#include <set>


/** A hashed struct */
struct A : public Hash::Hashed {
    /** Constructor */
    A(const Hash::Hash h) : Hashed { h } {}
};


/** Verify that hash singulars work */
void singular() {

    // Hashed
    auto s1 = std::make_shared<A>(0_ui);
    auto s2 = std::make_shared<A>(0_ui);
    auto s3 = std::make_shared<A>(1_ui);
    UNITTEST_ASSERT(Hash::singular(s1) == Hash::singular(s2))
    UNITTEST_ASSERT(Hash::singular(s1) != Hash::singular(s3))

    // Constexpr compilation tests
    constexpr auto c = Hash::singular("Hello");
    constexpr auto cui = Hash::singular(0_ui);
    constexpr auto ci = Hash::singular(0_i);

    // Non-constexpor compilation tests
    (void) Hash::singular(std::vector<Constants::Int> { 0_i, 1_i });
    (void) Hash::singular("Hello"s);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(hash)
