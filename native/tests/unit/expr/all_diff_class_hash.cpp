/**
 * @file
 * \ingroup unittest
 */
#include <set>
#include <testlib/testlib.hpp>


// For brevity
using namespace UnitTest::TestLib;


/** Add p's pointer to s */
template <typename T> void insert(std::set<Expr::Base *> &s, const Factory::Ptr<T> &p) {
    s.insert(
        const_cast<Expr::Base *const>(static_cast<const Expr::Base *const>(p.get()))); // NOLINT
}

/** Each construction should have a unique pointer and hash */
void all_diff_class_hash() {

    const auto a1 { Factories::t_literal<Expr::Bool>() };
    const auto a2 { Factories::t_literal<Expr::String>() };
    const auto a3 { Factories::t_literal<Expr::FP>() };
    const auto a4 { Factories::t_literal<Expr::BV>() };
    const auto a5 { Factories::t_literal<Expr::VS>() };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    hashes.insert(a1->hash);
    hashes.insert(a2->hash);
    hashes.insert(a3->hash);
    hashes.insert(a4->hash);
    hashes.insert(a5->hash);

    UNITTEST_ASSERT(hashes.size() == 5)

    // Verify unique pointers

    std::set<Expr::Base *> ptrs;
    insert(ptrs, a1);
    insert(ptrs, a2);
    insert(ptrs, a3);
    insert(ptrs, a4);
    insert(ptrs, a5);

    UNITTEST_ASSERT(ptrs.size() == 5)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(all_diff_class_hash)
