/**
 * @file
 * @brief Sanity checks that should pass
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Returns the passed argument by reference */
static U64 id_ref(const U64 &id) {
    return id;
}

/** A macro to help with testing */
#define TEST_TYPE(X)                                                                               \
    {                                                                                              \
        const auto s { Expr::X::static_cuid };                                                     \
        UNITTEST_ASSERT(s == id_ref(Expr::X::static_cuid));                                        \
        UNITTEST_ASSERT(s == UnitTest::TestLib::Factories::t_literal<Expr::X>(0)->cuid);           \
    }

/** A struct used to give friend access to unittests */
struct UnitTest::Friend {
    /** Cache Type */
    using Cache = Util::WeakCache<Hash::Hash, const Expr::Base>;
    /** The cache */
    const Cache &cache { Factory::Private::gcache<Expr::Base>() }; // NOLINT
    /** Get the cache gc_resize */
    [[nodiscard]] auto gc_resize() const { return cache.gc_resize; }
    /** Get the default cache gc_resize */
    [[nodiscard]] auto def() const { return Cache::gc_resize_default; }
};


/** Test sanity checks */
void sanity_check() {

    // Expr::X::static_cuid is defined at compile time of the shared library
    // by template meta-programming. Since it is calculated only within header files
    // when this test is compiled the compiler will independent calculate a value
    // for it when included by this test case. Since this value is not calculated
    // in a trivial manner and depend on macros such as __FILE__, in this test we
    // verify that the test case's calculation is consistent with the shared library's
    // in order to test that the calculation is reproducible and not so brittle
    // as to be dependent on directory location, something __FILE__ normally does.
    TEST_TYPE(Bool);
    TEST_TYPE(String);
    TEST_TYPE(VS);
    TEST_TYPE(BV);
    TEST_TYPE(FP);

    // Verify that the expr cache has been instantiated
    // If it was, the constructor sets gc_resize to gc_resize_default
    UnitTest::Friend wrapper;
    UNITTEST_ASSERT_MSG(wrapper.gc_resize() == wrapper.def(), "Cache failed to instantiate.");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(sanity_check)
