/** @file */

#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Each construction should have a unique pointer and hash */
int all_diff_class_hash() {

    Constants::Int z = 0;
    const auto a1 = literal_factory<ConcreteIntLiteral>(z);
    const auto a2 = literal_factory<ConcreteBoolLiteral>(z);
    const auto a3 = literal_factory<ConcreteStringLiteral>(z, z);
    const auto a4 = literal_factory<ConcreteFPLiteral>(z, z);
    const auto a5 = literal_factory<ConcreteBVLiteral>(z, z);
    const auto a6 = literal_factory<ConcreteVSLiteral>(z, z);

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    hashes.insert(a1->id);
    hashes.insert(a2->id);
    hashes.insert(a3->id);
    hashes.insert(a4->id);
    hashes.insert(a5->id);

    UNITTEST_ASSERT(hashes.size() == 5)

    // Verify unique pointers

    std::set<Raw::Base *> ids;
    ids.insert(a1.get());
    ids.insert(a2.get());
    ids.insert(a3.get());
    ids.insert(a4.get());
    ids.insert(a5.get());

    UNITTEST_ASSERT(ids.size() == 5)
    return 0;
}
