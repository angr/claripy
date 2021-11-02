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

    // Backend Constants
    auto z3_cpp { std::make_shared<Backend::Z3::Z3>() };
    const auto z3_manual { API::to_c(Util::Cast::Static::up<Backend::Base>(z3_cpp)) };
    UnitTest::Friend z3_priv { *z3_cpp };

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
    const auto bv_sym { Create::symbol<Expr::BV>("bv_sym", 64) };
    const auto vs { Create::literal(std::make_shared<PyObj::VS>(1, 2, 8)) };
    const auto bv_sym_with_ans { Create::symbol<Expr::BV>("bv_sym_with_ans", 64, make_an_vec()) };

    // Tests
    Util::Log::debug("Testing base funtions");
    UNITTEST_ASSERT(std::string { "z3" } == claricpp_backend_name(z3_manual));

    // Test handles
    const auto sum_c { API::copy_to_c(sum) };
    UNITTEST_ASSERT(claricpp_backend_handles(z3_manual, sum_c));
    UNITTEST_ASSERT(not claricpp_backend_handles(z3_manual, API::copy_to_c(vs)));

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
    UNITTEST_ASSERT(z3_priv.conv_cache_size() != 0);
    claricpp_backend_downsize(z3_manual);
    UNITTEST_ASSERT(z3_priv.conv_cache_size() == 0);

    // Test clearing persistent data
    (void) z3_cpp->simplify(bv_sym_with_ans.get()); // Populate satd
    UNITTEST_ASSERT(z3_priv.satd_cache_size() != 0);
    claricpp_backend_clear_persistent_data(z3_manual);
    UNITTEST_ASSERT(z3_priv.satd_cache_size() == 0);

    /********************************************************************/
    /*                                Z3                                */
    /********************************************************************/

    Util::Log::debug("Testing Z3 functions");

    // Test creating a z3 backend
    const auto z3 { claricpp_backend_z3_new() };

    // Test creating solvers
    const auto solver { claricpp_backend_z3_tls_solver(z3, 0) };
    UNITTEST_ASSERT(API::to_cpp(solver) != nullptr);
    const auto new_solver { claricpp_backend_z3_new_tls_solver(z3, 0) };
    UNITTEST_ASSERT(API::to_cpp(new_solver) != nullptr);
    UNITTEST_ASSERT(API::to_cpp(new_solver) != API::to_cpp(solver));
    const auto fst_solver_dup { claricpp_backend_z3_tls_solver(z3, 0) };
    UNITTEST_ASSERT(API::to_cpp(solver) == API::to_cpp(fst_solver_dup));

    const auto ugeq { [&bv_sym](const UInt i) {
        using C = Mode::Compare;
        return Create::compare<C::Unsigned | C::Greater | C::Eq>(bv_sym, Create::literal(i));
    } };
    const auto uleq { [&bv_sym](const UInt i) {
        using C = Mode::Compare;
        return Create::compare<C::Unsigned | C::Less | C::Eq>(bv_sym, Create::literal(i));
    } };
    z3::solver &z3_solver { API::to_cpp_ref(solver) };
    const ClaricppExpr geq3[] { API::to_c(ugeq(2)), API::to_c(ugeq(3)) }; // NOLINT
    const auto geq3_len { 2 };

    // Test add tracked
    claricpp_backend_z3_add_tracked(z3, solver, API::to_c(ugeq(1)));
    UNITTEST_ASSERT(z3_solver.assertions().size() == 1);
    //    UNITTEST_ASSERT(z3_solver.unsat_core().size() == 1);
    z3_solver.reset();

    claricpp_backend_z3_add_vec_tracked(z3, solver, geq3, 2);
    UNITTEST_ASSERT(z3_solver.assertions().size() == 2);
    //    UNITTEST_ASSERT(z3_solver.unsat_core().size() == 2);
    z3_solver.reset();

    // Test add untracked
    claricpp_backend_z3_add_untracked(z3, solver, API::to_c(ugeq(1)));
    UNITTEST_ASSERT(z3_solver.assertions().size() == 1);
    UNITTEST_ASSERT(z3_solver.unsat_core().size() == 0);
    z3_solver.reset();

    claricpp_backend_z3_add_vec_untracked(z3, solver, geq3, 2);
    UNITTEST_ASSERT(z3_solver.assertions().size() == 2);
    UNITTEST_ASSERT(z3_solver.unsat_core().size() == 0);
    z3_solver.reset();

    const auto cl { [](const UInt i) { return API::to_c(Create::literal(i)); } };
    const auto add { [&z3_cpp](z3::solver &s, Expr::BasePtr e) {
        z3_cpp->add<false>(s, e.get());
    } };

    // Test satisfiable
    add(z3_solver, Create::eq(one, one));
    UNITTEST_ASSERT(claricpp_backend_z3_satisfiable(z3, solver));
    z3_solver.push();
    add(z3_solver, Create::neq(one, one));
    UNITTEST_ASSERT(!claricpp_backend_z3_satisfiable(z3, solver));
    z3_solver.pop();
    UNITTEST_ASSERT(claricpp_backend_z3_satisfiable_ec(z3, solver, geq3, geq3_len));
    add(z3_solver, Create::eq(bv_sym, one));
    UNITTEST_ASSERT(!claricpp_backend_z3_satisfiable_ec(z3, solver, geq3, geq3_len));
    z3_solver.reset();

    // Test solution
    add(z3_solver, uleq(2));
    const auto bv_sym_c { API::copy_to_c(bv_sym) };
    UNITTEST_ASSERT(claricpp_backend_z3_solution(z3, bv_sym_c, cl(1), solver));
    UNITTEST_ASSERT(!claricpp_backend_z3_solution(z3, bv_sym_c, cl(3), solver));
    UNITTEST_ASSERT(!claricpp_backend_z3_solution_ec(z3, bv_sym_c, cl(3), solver, geq3, geq3_len));
    z3_solver.reset();
    UNITTEST_ASSERT(claricpp_backend_z3_solution_ec(z3, bv_sym_c, cl(3), solver, geq3, geq3_len));

    /********************************************************************/
    /*                             Concrete                             */
    /********************************************************************/
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backend)
