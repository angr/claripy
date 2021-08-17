/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

/** Return true if x is a T equal to sol */
template <typename T> static bool test_eq(const Backend::Z3::PrimVar x, const T y) {
    try {
        UNITTEST_ASSERT(std::get<T>(x) == y);
        return true;
    }
    catch (std::bad_variant_access &) {
        return false;
    };
}

struct UnitTest::ClaricppUnitTest {
    /** A helper function for abstract_to_prim */
    template <typename T> static auto prep(Backend::Z3::Z3 &z3, T in) {
        return z3.abstract_to_prim(z3.convert(Create::literal(std::move(in))));
    }
};

/** Verify that abstract_to_primitive is working for input in of type T */
template <typename T> static bool test(Backend::Z3::Z3 &z3, const T in) {
    return test_eq(UnitTest::ClaricppUnitTest::prep(z3, in), in);
}

/** Verify that abstract_to_primitive is working for floating point type T */
template <typename T> static void test_f(Backend::Z3::Z3 &z3) {
    static_assert(Utils::qualified_is_in<T, float, double>, "Unsupported floating point type");
    UNITTEST_ASSERT(test(z3, T { 10. }));
    UNITTEST_ASSERT(test(z3, T { 0. }));
    UNITTEST_ASSERT(test(z3, T { -0. }));
    UNITTEST_ASSERT(test(z3, std::numeric_limits<T>::infinity()));
    UNITTEST_ASSERT(test(z3, -std::numeric_limits<T>::infinity())); // safe for double / float
    UNITTEST_ASSERT(test(z3, Backend::Z3::nan<T>));
}


/** Try to abstract_to_prim a claricpp expression from z3 */
void abstract_to_prim() {
    z3::context ctx;
    auto z3 { Backend::Z3::Z3 {} };

    Utils::Log::debug("Testing bool...");
    UNITTEST_ASSERT(test(z3, true));
    UNITTEST_ASSERT(test(z3, false));

    Utils::Log::debug("Testing BV...");
    UNITTEST_ASSERT(test(z3, uint8_t { 10 }));
    UNITTEST_ASSERT(test(z3, uint16_t { 10 }));
    UNITTEST_ASSERT(test(z3, uint32_t { 10 }));
    UNITTEST_ASSERT(test(z3, uint64_t { 10 }));
    UNITTEST_ASSERT(test(z3, BigInt { 64, 64 }));

    Utils::Log::debug("Testing floats...");
    test_f<float>(z3);

    Utils::Log::debug("Testing doubles...");
    test_f<double>(z3);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abstract_to_prim)
