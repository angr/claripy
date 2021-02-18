/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


// For brevity
namespace Ex = Expression;
using namespace UnitTest::TestLib;

/** Construct a t_literal<T> and up-cast it */
template <typename T> Ex::BasePtr construct(const Constants::Int i) {
    return Factories::t_literal<T>(i);
}

/** Each construction should have a unique pointer and hash */
void diff() {

    const std::vector<Ex::BasePtr> objs {
        // Round 1
        construct<Ex::Bool>(0_i), construct<Ex::String>(0_i), construct<Ex::FP>(0_i),
        construct<Ex::BV>(0_i), construct<Ex::VS>(0_i),
        // Round 2
        construct<Ex::Bool>(1_i), construct<Ex::String>(1_i), construct<Ex::FP>(1_i),
        construct<Ex::BV>(1_i), construct<Ex::VS>(1_i)
    };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    for (const auto &i : objs) {
        hashes.insert(i->hash);
    }

    UNITTEST_ASSERT(hashes.size() == objs.size())

    // Verify unique pointers

    std::set<Ex::Base *> ptrs;
    for (const auto &i : objs) {
        ptrs.insert(const_cast<Ex::Base *>(i.get())); // NOLINT
    }

    UNITTEST_ASSERT(ptrs.size() == objs.size())
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(diff)
