/**
 * @file
 * \ingroup unittest
 */
#include <set>
#include <testlib/testlib.hpp>


// For brevity
using namespace UnitTest::TestLib;


/** Construct a t_literal<T> and up-cast it */
template <typename T> Expr::BasePtr construct(const I64 i = 0) {
    auto ret { Factories::t_literal<T>(i) };
    return Util::PCast::Static::up<Expr::Base>(ret);
}

/** Each construction should have a unique pointer and hash */
void same() {

    const std::vector<Expr::BasePtr> objs {
        // Round 1
        construct<Expr::Bool>(), construct<Expr::String>(), construct<Expr::FP>(),
        construct<Expr::BV>(), construct<Expr::VS>(),
        // Round 2
        construct<Expr::Bool>(), construct<Expr::String>(), construct<Expr::FP>(),
        construct<Expr::BV>(), construct<Expr::VS>()
    };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    for (const auto &i : objs) {
        hashes.insert(i->hash);
    }

    UNITTEST_ASSERT(hashes.size() == objs.size() / 2);

    // Verify unique pointers

    std::set<Expr::Base *> ptrs;
    for (const auto &i : objs) {
        ptrs.insert(const_cast<Expr::Base *>(i.get())); // NOLINT
    }

    UNITTEST_ASSERT(ptrs.size() == objs.size() / 2);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(same)
