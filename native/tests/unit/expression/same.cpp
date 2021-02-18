/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
namespace Ex = Expression;
using namespace UnitTest::TestLib;


/** Construct a t_literal<T> and up-cast it */
template <typename T> Ex::BasePtr construct(const Constants::Int i = 0) {
    auto ret { Factories::t_literal<T>(i) };
    return Utils::up_cast<Ex::Base>(ret);
}

/** Each construction should have a unique pointer and hash */
void same() {

    const std::vector<Ex::BasePtr> objs {
        // Round 1
        construct<Ex::Bool>(), construct<Ex::Bool>(), construct<Ex::String>(), construct<Ex::FP>(),
        construct<Ex::BV>(), construct<Ex::VS>(),
        // Round 2
        construct<Ex::Bool>(), construct<Ex::Bool>(), construct<Ex::String>(), construct<Ex::FP>(),
        construct<Ex::BV>(), construct<Ex::VS>()
    };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    for (const auto &i : objs) {
        hashes.insert(i->hash);
    }

    UNITTEST_ASSERT(hashes.size() == objs.size() / 2)

    // Verify unique pointers

    std::set<Ex::Base *> ptrs;
    for (const auto &i : objs) {
        ptrs.insert(const_cast<Ex::Base *>(i.get())); // NOLINT
    }

    UNITTEST_ASSERT(ptrs.size() == objs.size() / 2)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(same)
