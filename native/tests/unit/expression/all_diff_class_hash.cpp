/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Add p's pointer to s */
template <typename T>
void insert(std::set<Base*>& s, const Factory::Ptr<T>& p) {
	s.insert(const_cast<Base* const>(static_cast<const Base * const>(p.get()))); // NOLINT
}

/** Each construction should have a unique pointer and hash */
void all_diff_class_hash() {

    const auto a1 { Factories::t_literal<Int>() };
    const auto a2 { Factories::t_literal<Bool>() };
    const auto a3 { Factories::t_literal<String>() };
    const auto a4 { Factories::t_literal<FP>() };
    const auto a5 { Factories::t_literal<BV>() };
    const auto a6 { Factories::t_literal<VS>() };

    // Verify unique hashes

    std::set<Hash::Hash> hashes;
    hashes.insert(a1->hash);
    hashes.insert(a2->hash);
    hashes.insert(a3->hash);
    hashes.insert(a4->hash);
    hashes.insert(a5->hash);
    hashes.insert(a6->hash);

    UNITTEST_ASSERT(hashes.size() == 6)

    // Verify unique pointers

    std::set<Base*> ptrs;
    insert(ptrs, a1);
    insert(ptrs, a2);
    insert(ptrs, a3);
    insert(ptrs, a4);
    insert(ptrs, a5);
    insert(ptrs, a6);

    UNITTEST_ASSERT(ptrs.size() == 6)
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(all_diff_class_hash)
