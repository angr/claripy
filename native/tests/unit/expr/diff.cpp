/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


// For brevity
using namespace UnitTest::TestLib;

/** Construct a t_literal<T> and up-cast it */
template <typename T> Expr::BasePtr construct(const I64 i) {
    return Factories::t_literal<T>(i);
}

/** Each construction should have a unique pointer and hash */
void diff() {

    const std::vector<Expr::BasePtr> objs {
        // Round 1
        construct<Expr::Bool>(0_i), construct<Expr::String>(0_i), construct<Expr::FP>(0_i),
        construct<Expr::BV>(0_i), construct<Expr::VS>(0_i),
        // Round 2
        construct<Expr::Bool>(1_i), construct<Expr::String>(1_i), construct<Expr::FP>(1_i),
        construct<Expr::BV>(1_i), construct<Expr::VS>(1_i)
    };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    for (const auto &i : objs) {
        hashes.insert(i->hash);
    }

    UNITTEST_ASSERT(hashes.size() == objs.size());

    // Verify unique pointers

    std::set<Expr::Base *> ptrs;
    for (const auto &i : objs) {
        ptrs.insert(const_cast<Expr::Base *>(i.get())); // NOLINT
    }

    UNITTEST_ASSERT(ptrs.size() == objs.size());
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(diff)
