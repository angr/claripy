/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** A class which can check Z3's private internals */
struct UnitTest::Friend final {
    /** The z3 backend to extract data from */
    Backend::Z3::Z3 &z3;
    /** Get the conversion cache size */
    auto conv_cache_size() { return z3.conversion_cache_g().size(); }
    /** Get the satd cache size */
    auto satd_cache_size() { return z3.tls.symbol_annotation_translocation_data.size(); }
};

/** Verify the Backend API works */
void backend() {

    /********************************************************************/
    /*                               Base                               */
    /********************************************************************/

    // Annotation constants
    using AnVec = Annotation::Vec;
    using RawVec = AnVec::RawVec;
    const auto base_an { Annotation::factory<Annotation::Base>() };
    auto make_an_vec { [&base_an]() { return std::make_shared<AnVec>(RawVec { base_an }); } };

    // Create Constants
    const auto one { Create::literal(1_ui) };
    const auto two { Create::literal(2_ui) };
    const auto sum { Create::add({ one, one }) };
    const auto vs { Create::literal(std::make_shared<PyObj::VS>(1, 2, 8)) };
    const auto bv_sym_with_ans { Create::symbol<Expr::BV>("bv_sym", 64, make_an_vec()) };

    // Backend Constants
    auto &z3_cpp { *new Backend::Z3::Z3 }; // NOLINT
    const auto z3_manual { API::to_c(&static_cast<Backend::Base &>(z3_cpp)) };

    // Tests
    Util::Log::debug("Testing base funtions");
    UNITTEST_ASSERT(std::string { "z3" } == claricpp_backend_name(z3_manual));

    // Test handles
    const auto sum_c { API::copy_to_c(sum) };
    UNITTEST_ASSERT(claricpp_backend_handles(z3_manual, sum_c));
    UNITTEST_ASSERT(not claricpp_backend_handles(z3_manual, API::copy_to_c(vs)));
    Util::Log::info("Desired error detected: success.");

    // Test simplify
    UNITTEST_ASSERT(API::to_cpp(claricpp_backend_simplify(z3_manual, sum_c))->hash == two->hash);

    // Test BigInt mode functions
    const auto old_mode { claricpp_backend_get_big_int_mode() };
    const auto got_mode { claricpp_backend_set_big_int_mode(ClaricppBimInt) };
    const auto new_mode { claricpp_backend_get_big_int_mode() };
    UNITTEST_ASSERT(old_mode == ClaricppBimStr); // This should be default
    UNITTEST_ASSERT(old_mode == got_mode);       // This should be default
    UNITTEST_ASSERT(new_mode == ClaricppBimInt); // This should be default
    claricpp_backend_set_big_int_mode(old_mode); // Restore for future tests

    // Test downsizing backend data
    UnitTest::Friend priv { z3_cpp };
    UNITTEST_ASSERT(priv.conv_cache_size() != 0);
    claricpp_backend_downsize(z3_manual);
    UNITTEST_ASSERT(priv.conv_cache_size() == 0);

    // Test clearing persistent data
    (void) z3_cpp.simplify(bv_sym_with_ans.get()); // Populate satd
    UNITTEST_ASSERT(priv.satd_cache_size() != 0);
    claricpp_backend_clear_persistent_data(z3_manual);
    UNITTEST_ASSERT(priv.satd_cache_size() == 0);

    /********************************************************************/
    /*                                Z3                                */
    /********************************************************************/

    Util::Log::debug("Testing Z3 functions");

    // Test creating a z3 backend
    const auto z3 { claricpp_backend_z3_new() };
    (void) z3;

    /********************************************************************/
    /*                             Concrete                             */
    /********************************************************************/
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backend)
