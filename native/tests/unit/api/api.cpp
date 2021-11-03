/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the API's basic functionality works */
void api() {

    // C++
    const auto lit { Create::literal(1_ui) };
    auto old_uc { lit.use_count() };

    // C
    auto moved_c { API::to_c(std::remove_const_t<decltype(lit)> { lit }) };
    auto copied_c { API::copy_to_c(lit) };
    UNITTEST_ASSERT(lit.use_count() == old_uc + 2);

    // New scope for references
    {
        // Return to C++
        auto &moved { API::to_cpp(moved_c) };
        auto &copied { API::to_cpp(copied_c) };
        UNITTEST_ASSERT(lit.use_count() == old_uc + 2);

        // Checks
        UNITTEST_ASSERT(moved == lit);
        UNITTEST_ASSERT(copied == lit);

        // Free
        claricpp_free_expr(&moved_c);
        claricpp_free_expr(&copied_c);

        // moved and copied should be dangling references now
        // We get rid of them via scope
    }

    // Checks
    UNITTEST_ASSERT(moved_c.ptr == nullptr);
    UNITTEST_ASSERT(copied_c.ptr == nullptr);
    UNITTEST_ASSERT(lit.use_count() == old_uc);

    // Create Array
    const std::vector<Expr::BasePtr> vec { lit, lit };
    old_uc = lit.use_count();
    auto arr_c { API::to_arr(std::remove_const_t<decltype(vec)> { vec }) };

    // Test array
    UNITTEST_ASSERT(lit.use_count() == old_uc + static_cast<decltype(old_uc)>(vec.size()));
    UNITTEST_ASSERT(arr_c.len == vec.size());
    for (SIZE_T i { 0 }; i < vec.size(); ++i) {
        UNITTEST_ASSERT(API::to_cpp(arr_c.arr[i]) == vec[i]);
    }

    // Free array
    claricpp_free_array_expr(&arr_c);
    UNITTEST_ASSERT(arr_c.len == 0);
    UNITTEST_ASSERT(arr_c.arr == nullptr);
    UNITTEST_ASSERT(lit.use_count() == old_uc);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(api)
