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
int all_diff_class_hash() {

    const auto a1 = literal_factory<ConcreteIntLiteral>(0_i);
    const auto a2 = literal_factory<ConcreteBoolLiteral>(0_i);
    const auto a3 = literal_factory<ConcreteStringLiteral>(0_i);
    const auto a4 = literal_factory<ConcreteFPLiteral>(0_i);
    const auto a5 = literal_factory<ConcreteBVLiteral>(0_i);
    const auto a6 = literal_factory<ConcreteVSLiteral>(0_i);

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
