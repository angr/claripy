/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Verify the Backend API works */
void backend() {

    /********************************************************************/
    /*                               Base                               */
    /********************************************************************/

    // Constants
    const auto one { Create::literal(1_ui) };
    const auto two { Create::literal(2_ui) };
    const auto sum { Create::add({ one, one }) };
    const auto z3 { API::to_c(static_cast<Backend::Base *const>(new Backend::Z3::Z3)) }; // NOLINT
    const auto vs { Create::literal(std::make_shared<PyObj::VS>(1, 2, 8)) };

    UNITTEST_ASSERT(std::string { "z3" } == claricpp_backend_name(z3));

    UNITTEST_ASSERT(claricpp_backend_handles(z3, API::copy_to_c(sum)));
    UNITTEST_ASSERT(not claricpp_backend_handles(z3, API::copy_to_c(vs)));
    Util::Log::info("Desired error detected: success.");

    UNITTEST_ASSERT(API::to_cpp(claricpp_backend_simplify(z3, API::copy_to_c(sum)))->hash ==
                    two->hash);

    const auto old_mode { claricpp_backend_get_big_int_mode() };
    const auto got_mode { claricpp_backend_set_big_int_mode(ClaricppBimInt) };
    const auto new_mode { claricpp_backend_get_big_int_mode() };
    UNITTEST_ASSERT(old_mode == ClaricppBimStr); // This should be default
    UNITTEST_ASSERT(old_mode == got_mode);       // This should be default
    UNITTEST_ASSERT(new_mode == ClaricppBimInt); // This should be default
    claricpp_backend_set_big_int_mode(old_mode); // Restore for future tests

#if 0
    void claricpp_backend_downsize(const ClaricppBackend bk);
    void claricpp_backend_clear_persistent_data(const ClaricppBackend bk);
#endif

    /********************************************************************/
    /*                                Z3                                */
    /********************************************************************/

    /********************************************************************/
    /*                             Concrete                             */
    /********************************************************************/
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backend)
