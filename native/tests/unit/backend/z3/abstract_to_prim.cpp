/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Return true if x is a T equal to sol */
template <typename T> static bool test_eq(const Op::PrimVar x, const T y) {
    try {
        UNITTEST_ASSERT(std::get<T>(x) == y);
        return true;
    }
    catch (std::bad_variant_access &) {
        return false;
    };
}

struct UnitTest::Friend {
    /** A helper function for abstract_to_prim */
    template <typename T> static auto prep(Backend::Z3::Z3 &z3, T in) {
        const auto e { Create::literal(std::move(in)) };
        return z3.abstract_to_prim(z3.convert(e.get()));
    }
};

/** Verify that abstract_to_primitive is working for input in of type T */
template <typename T> static bool test(Backend::Z3::Z3 &z3, const T in) {
    return test_eq(UnitTest::Friend::prep(z3, in), in);
}

/** Verify that abstract_to_primitive is working for floating point type T */
template <typename T> static void test_f(Backend::Z3::Z3 &z3) {
    static_assert(Util::Type::Is::in<T, float, double>, "Unsupported floating point type");
    UNITTEST_ASSERT(test(z3, T { 10. }));
    UNITTEST_ASSERT(test(z3, T { 0. }));
    UNITTEST_ASSERT(test(z3, T { -0. }));
    UNITTEST_ASSERT(test(z3, std::numeric_limits<T>::infinity()));
    UNITTEST_ASSERT(test(z3, -std::numeric_limits<T>::infinity())); // safe for double / float
    // NaNs are never equal so:
    auto var { UnitTest::Friend::prep(z3, Backend::Z3::nan<T>) };
    try {
        UNITTEST_ASSERT(std::isnan(std::get<T>(var)));
    }
    catch (std::bad_variant_access &) {
        UNITTEST_ERR("Variant is not a T");
    };
}


/** Try to abstract_to_prim a claricpp expr from z3 */
void abstract_to_prim() {
    auto z3 { Backend::Z3::Z3 {} };

    Util::Log::debug("Testing bool...");
    UNITTEST_ASSERT(test(z3, true));
    UNITTEST_ASSERT(test(z3, false));

    Util::Log::debug("Testing BV...");
    UNITTEST_ASSERT(test(z3, uint8_t { 10 }));
    UNITTEST_ASSERT(test(z3, uint16_t { 10 }));
    UNITTEST_ASSERT(test(z3, uint32_t { 10 }));
    UNITTEST_ASSERT(test(z3, U64 { 10 }));
    UNITTEST_ASSERT(test(z3, BigInt { "20", 128 })); // > 64

    Util::Log::debug("Testing floats...");
    test_f<float>(z3);

    Util::Log::debug("Testing doubles...");
    test_f<double>(z3);

#if 0
    Util::Log::debug("Testing strings...");
    // @todo String testing
#endif
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(abstract_to_prim)
