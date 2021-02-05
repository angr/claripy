/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Construct a t_literal<T> and up-cast it */
template <typename T> Factory::Ptr<Expression::Base> construct(const Constants::Int i = 0) {
    auto ret { Factories::t_literal<T>(i) };
    return Utils::up_cast<Expression::Base>(ret);
}

/** Each construction should have a unique pointer and hash */
void same() {

    const std::vector<Factory::Ptr<Expression::Base>> objs {
        // Round 1
        construct<Int>(), construct<Bool>(), construct<String>(), construct<FP>(), construct<BV>(),
        construct<VS>(),
        // Round 2
        construct<Int>(), construct<Bool>(), construct<String>(), construct<FP>(), construct<BV>(),
        construct<VS>()
    };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    for (const auto &i : objs) {
        hashes.insert(i->hash);
    }

    UNITTEST_ASSERT(hashes.size() == objs.size() / 2)

    // Verify unique pointers

    std::set<Constants::CTSC<Base>> ptrs;
    for (const auto &i : objs) {
        hashes.insert(i.get());
    }

    UNITTEST_ASSERT(ptrs.size() == objs.size() / 2)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(same)
