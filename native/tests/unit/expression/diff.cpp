/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;

/** Construct a t_literal<T> and up-cast it */
template <typename T> BasePtr construct(const Constants::Int i) {
    return Factories::t_literal<T>(i);
}

/** Each construction should have a unique pointer and hash */
void diff() {

    const std::vector<BasePtr> objs {
        // Round 1
        construct<Int>(0_i), construct<Bool>(0_i), construct<String>(0_i), construct<FP>(0_i),
        construct<BV>(0_i), construct<VS>(0_i),
        // Round 2
        construct<Int>(1_i), construct<Bool>(1_i), construct<String>(1_i), construct<FP>(1_i),
        construct<BV>(1_i), construct<VS>(1_i)
    };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    for (const auto &i : objs) {
        hashes.insert(i->hash);
    }

    UNITTEST_ASSERT(hashes.size() == objs.size())

    // Verify unique pointers

    std::set<Base *> ptrs;
    for (const auto &i : objs) {
        ptrs.insert(const_cast<Base *>(i.get())); // NOLINT
    }

    UNITTEST_ASSERT(ptrs.size() == objs.size())
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(diff)
