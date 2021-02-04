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
    A(const Hash::Hash h) noexcept : Hashed { h } {}
};


/** Verify that hash singulars work */
void singular() {

    // Hashed
    auto s1 = std::make_shared<const A>(0_ui);
    auto s2 = std::make_shared<const A>(0_ui);
    auto s3 = std::make_shared<const A>(1_ui);
    UNITTEST_ASSERT(Hash::singular(s1) == Hash::singular(s2))
    UNITTEST_ASSERT(Hash::singular(s1) != Hash::singular(s3))

    // Constexpr compilation tests
    constexpr Constants::CCSC msg { "Hello" };
    constexpr auto c = Hash::singular(msg);
    constexpr auto cui = Hash::singular(0_ui);
    constexpr auto ci = Hash::singular(0_i);
    Utils::sink(c, cui, ci);

    // Non-constexpor compilation tests
    (void) Hash::singular(std::vector<Constants::Int> { 0_i, 1_i });
    const std::string sref { "Hello" };
    (void) Hash::singular(sref);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(singular)
