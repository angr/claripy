/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify bit_mask members work; this is really just a compile test because constexpr */
void bit_mask() {
    using C = Mode::Compare;
    const auto has = Util::BitMask::has<C>;
    const auto has_any = Util::BitMask::has_any<C>;

    // has

    // ID
    UNITTEST_ASSERT(has(C::Less, C::Less));

    // Different
    UNITTEST_ASSERT(!has(C::Less, C::Greater));

    // Is in
    UNITTEST_ASSERT(has(C::Less | C::Eq, C::Less));

    // Not is in
    UNITTEST_ASSERT(!has(C::Less | C::Eq, C::Greater));

    // Multiple id
    UNITTEST_ASSERT(has(C::Less | C::Eq, C::Less | C::Eq));

    // Multiple diff
    UNITTEST_ASSERT(!has(C::Less | C::Eq, C::Greater | C::Neq));

    // Multiple in
    UNITTEST_ASSERT(has(C::Signed | C::Less | C::Eq, C::Less | C::Eq));

    // Multiple not in
    UNITTEST_ASSERT(!has(C::Signed | C::Less | C::Eq, C::Greater | C::Neq));

    // Some in, some not
    UNITTEST_ASSERT(!has(C::Signed | C::Less | C::Eq, C::Less | C::Neq));

    // has any

    // ID
    UNITTEST_ASSERT(has_any(C::Less, C::Less));

    // Different
    UNITTEST_ASSERT(!has_any(C::Less, C::Greater));

    // Is in
    UNITTEST_ASSERT(has_any(C::Less | C::Eq, C::Less));

    // One is in
    UNITTEST_ASSERT(has_any(C::Less, C::Eq | C::Less));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(bit_mask)
