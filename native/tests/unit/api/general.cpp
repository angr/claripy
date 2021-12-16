/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the API's basic functionality works */
void general() {

    /********************************************************************/
    /*                            Non-Arrays                            */
    /********************************************************************/

    // C++
    const auto bv1 { Create::literal(1_ui) };
    auto old_uc { bv1.use_count() };

    // C
    auto moved_c { API::to_c(std::remove_const_t<decltype(bv1)> { bv1 }) };
    auto copied_c { API::copy_to_c(bv1) };
    UNITTEST_ASSERT(bv1.use_count() == old_uc + 2); // NOLINT (false positive)

    // New scope for references
    {
        // Return to C++
        auto &moved { API::to_cpp(moved_c) };
        auto &copied { API::to_cpp(copied_c) };
        UNITTEST_ASSERT(bv1.use_count() == old_uc + 2);

        // Checks
        UNITTEST_ASSERT(moved == bv1);
        UNITTEST_ASSERT(copied == bv1);

        // moved and copied should be dangling references now
        // We get rid of them via scope
    }

    // Free
    claricpp_free_expr(&moved_c);
    claricpp_free_expr(&copied_c);
    UNITTEST_ASSERT(moved_c.ptr == nullptr);
    UNITTEST_ASSERT(copied_c.ptr == nullptr);
    UNITTEST_ASSERT(bv1.use_count() == old_uc);

    // Double free (memcheck test but should be a nop)
    claricpp_free_expr(&moved_c);
    claricpp_free_expr(&copied_c);
    UNITTEST_ASSERT(moved_c.ptr == nullptr);
    UNITTEST_ASSERT(copied_c.ptr == nullptr);
    UNITTEST_ASSERT(bv1.use_count() == old_uc); // Just in case something catastrophic happens

    /********************************************************************/
    /*                              Unions                              */
    /********************************************************************/

    // Create, translate, and free Prim string
    const Op::PrimVar prim { std::string("Hello") };
    auto prim_c { API::copy_to_c(prim) }; // Should dynamically allocate memory
    UNITTEST_ASSERT(prim_c.type == ClaricppTypeEnumStr);
    UNITTEST_ASSERT(std::strlen(prim_c.data.str) == std::get<std::string>(prim).size()); // NOLINT
    UNITTEST_ASSERT(std::string(prim_c.data.str) == std::get<std::string>(prim));        // NOLINT
    claricpp_free_prim(&prim_c);
    UNITTEST_ASSERT(prim_c.data.str == nullptr); // NOLINT

    // Repeat Arg and expr
    old_uc = bv1.use_count();
    const Op::ArgVar arg { bv1 };
    UNITTEST_ASSERT(bv1.use_count() == old_uc + 1);
    old_uc = bv1.use_count();
    auto arg_c { API::copy_to_c(arg) };
    UNITTEST_ASSERT(bv1.use_count() == old_uc + 1);
    UNITTEST_ASSERT(arg_c.type == ClaricppTypeEnumExpr);
    UNITTEST_ASSERT(API::to_cpp(arg_c.data.expr) == bv1); // NOLINT
    old_uc = bv1.use_count();
    claricpp_free_arg(&arg_c);
    UNITTEST_ASSERT(bv1.use_count() + 1 == old_uc);

    /********************************************************************/
    /*                              Arrays                              */
    /********************************************************************/

    // Create array of Exprs
    const std::vector<Expr::BasePtr> vec { bv1, bv1 };
    old_uc = bv1.use_count();
    auto arr_c { API::copy_to_arr(vec) }; // NOLINT

    // Test array of Exprs
    UNITTEST_ASSERT(bv1.use_count() == old_uc + static_cast<decltype(old_uc)>(vec.size()));
    UNITTEST_ASSERT(arr_c.len == vec.size());
    for (SIZE_T i { 0 }; i < vec.size(); ++i) {
        UNITTEST_ASSERT(API::to_cpp(arr_c.arr[i]) == vec[i]); // NOLINT (false positive)
    }

    // Free array of Exprs
    claricpp_free_array_expr(&arr_c);
    UNITTEST_ASSERT(arr_c.len == 0);
    UNITTEST_ASSERT(arr_c.arr == nullptr);
    UNITTEST_ASSERT(bv1.use_count() == old_uc);

    // Create array of Args containing Exprs
    const std::vector<Op::ArgVar> arg_vec { bv1, bv1 };
    old_uc = bv1.use_count();
    auto arg_vec_c { API::copy_to_arr(arg_vec) };

    // Test array of Args containing Exprs
    UNITTEST_ASSERT(bv1.use_count() == old_uc + 2);
    UNITTEST_ASSERT(arg_vec_c.len == 2);
    for (UInt i { 0 }; i < arg_vec_c.len; ++i) {
        UNITTEST_ASSERT(arg_vec_c.arr[i].type == ClaricppTypeEnumExpr);  // NOLINT
        UNITTEST_ASSERT(API::to_cpp(arg_vec_c.arr[i].data.expr) == bv1); // NOLINT
    }

    // Free array of Args containing Exprs
    claricpp_free_array_arg(&arg_vec_c);
    UNITTEST_ASSERT(bv1.use_count() == old_uc);
    UNITTEST_ASSERT(arg_vec_c.arr == nullptr);
    UNITTEST_ASSERT(arg_vec_c.len == 0);

    /********************************************************************/
    /*                          Double Arrays                           */
    /********************************************************************/

    // Create a double array
    const std::vector<Op::PrimVar> prim_vec { prim, prim };
    const std::vector<std::vector<Op::PrimVar>> double_prim_vec { prim_vec, prim_vec };

    // Translate it to C + error check
    auto double_prim_vec_c { API::copy_to_double_arr(double_prim_vec) }; // NOLINT
    UNITTEST_ASSERT(double_prim_vec_c.len == double_prim_vec.size());
    for (UInt i { 0 }; i < double_prim_vec.size(); ++i) {
        auto &dpvci { double_prim_vec_c.arr[i] }; // NOLINT
        UNITTEST_ASSERT(dpvci.len == double_prim_vec[i].size());
        for (UInt k { 0 }; k < dpvci.len; ++k) {
            UNITTEST_ASSERT(dpvci.arr[k].type == ClaricppTypeEnumStr); // NOLINT
            const std::string str { dpvci.arr[k].data.str };           // NOLINT
            const auto &var { std::get<std::string>(double_prim_vec[i][k]) };
            UNITTEST_ASSERT(str.size() == var.size());
            UNITTEST_ASSERT(str == var);
        }
    }

    // Free it
    claricpp_free_double_array_prim(&double_prim_vec_c);
    UNITTEST_ASSERT(double_prim_vec_c.arr == nullptr);
    UNITTEST_ASSERT(double_prim_vec_c.len == 0);

    /********************************************************************/
    /*                            Exceptions                            */
    /********************************************************************/

    // Preliminary test
    UNITTEST_ASSERT(!claricpp_has_exception());

    // Test generating an exception
    (void) claricpp_create_not(API::copy_to_c(bv1), { nullptr });
    UNITTEST_ASSERT(claricpp_has_exception());

    // Test retrieving an exception
    auto exception { claricpp_get_exception() };
    UNITTEST_ASSERT(!claricpp_has_exception()); // Getting should clear it

    // Verify exception
    UNITTEST_ASSERT(exception.type == ClaricppExceptionEnumPython);
    UNITTEST_ASSERT(std::strstr(exception.msg, "invalid type") != nullptr);
    UNITTEST_ASSERT(std::strstr(exception.trace, "general") != nullptr);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(general)
