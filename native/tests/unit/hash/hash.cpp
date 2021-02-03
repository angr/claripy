/**
 * @file
 * \ingroup unittest
 */
#include "hash.hpp"

#include "testlib.hpp"

#include <set>


// For brevity
using namespace Hash;


/** A hashed struct */
struct A : public Hashed {
    /** Constructor */
    A(const Hash h) : Hashed { h } {}
};


/** Verify that hashing of multiple objects works */
void hash() {
    std::set<Hash> hashes;

    // Values to use
    const A a0 { 0_ui };
    const A a1 { 1_ui };
    const std::string hi_s { "hi" };
    const Constants::CCSC hi_c { "hi" };
    const std::vector<A> vec1 { a0, a1 };
    const std::vector<A> vec2 { a1, a0 };
    const Constants::UInt uz { 0_ui };
    const Constants::Int z { 0_i };

    // Hash multiple things

    hashes.insert(hash(a0, hi_s, z)); // 1
    hashes.insert(hash(a0, hi_s, z)); // 1

    hashes.insert(hash(a0, hi_s, zu)); // 2

    hashes.insert(hash(vec1)); // 3

    hashes.insert(hash(vec2)); // 4

    hashes.insert(hash(hi_s, hi_c)); // 5
    hashes.insert(hash(hi_s, hi_c)); // 5

    hashes.insert(hash(hi_c, hi_s)); // 6
    hashes.insert(hash(hi_c, hi_s)); // 6

    hashes.insert(hash(a0)); // 7

    hashes.insert(hash(a1)); // 8

    // Verify uniqueness
    UNITTEST_ASSERT(hashes.size() == 8)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(hash)
