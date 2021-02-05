/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Each construction should have a unique pointer and hash */
void all_diff_class_hash() {

    const auto a1 { literal_factory<ConcreteIntLiteral>(0_i) };
    const auto a2 { literal_factory<ConcreteBoolLiteral>(0_i) };
    const auto a3 { literal_factory<ConcreteStringLiteral>(0_i) };
    const auto a4 { literal_factory<ConcreteFPLiteral>(0_i) };
    const auto a5 { literal_factory<ConcreteBVLiteral>(0_i) };
    const auto a6 { literal_factory<ConcreteVSLiteral>(0_i) };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    hashes.insert(a1->hash);
    hashes.insert(a2->hash);
    hashes.insert(a3->hash);
    hashes.insert(a4->hash);
    hashes.insert(a5->hash);

    UNITTEST_ASSERT(hashes.size() == 5)

    // Verify unique pointers

    std::set<Raw::Base *> ptrs;
    ptrs.insert(a1.get());
    ptrs.insert(a2.get());
    ptrs.insert(a3.get());
    ptrs.insert(a4.get());
    ptrs.insert(a5.get());

    UNITTEST_ASSERT(ptrs.size() == 5)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(all_diff_class_hash)
