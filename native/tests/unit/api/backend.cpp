/**
 * @file
 * \ingroup unittest
 */
#include "exc.hpp"
#include "testlib.hpp"


/** A class which can check Z3's private internals */
struct UnitTest::Friend final {
    /** The z3 backend to extract data from */
    Backend::Z3::Z3 &z3; // NOLINT (intentional exposure)
    /** Get the conversion cache size */
    auto conv_cache_size() { return z3.conversion_cache_g().size(); } // NOLINT
    /** Get the satd cache size */
    auto satd_cache_size() { return z3.tls.symbol_annotation_translocation_data.size(); } // NOLINT
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
    const auto bv_neq_bv { Create::neq(bv_sym, bv_sym) };

    // Tests
    Util::Log::debug("Testing base funtions");
    Util::Log::debug("  - name");
    UNITTEST_ASSERT(std::string { "z3" } == exc(claricpp_backend_name(z3_manual)));

    // Test handles
    Util::Log::debug("  - handles");
    const auto sum_c { API::copy_to_c(sum) };
    UNITTEST_ASSERT(exc(claricpp_backend_handles(z3_manual, sum_c)));
    UNITTEST_ASSERT(!exc(claricpp_backend_handles(z3_manual, API::copy_to_c(vs))));

    // Test simplify
    Util::Log::debug("  - simplify"); // NOLINT (false positive, not a leak)
    UNITTEST_ASSERT(API::to_cpp(exc(claricpp_backend_simplify(z3_manual, sum_c)))->hash ==
                    two->hash);

    // Test BigInt mode functions
    Util::Log::debug("  - big int");
    const auto old_mode { exc(claricpp_backend_get_big_int_mode()) };
    const auto got_mode { exc(claricpp_backend_set_big_int_mode(ClaricppBimInt)) };
    const auto new_mode { exc(claricpp_backend_get_big_int_mode()) };
    UNITTEST_ASSERT(old_mode == ClaricppBimStr);      // This should be default
    UNITTEST_ASSERT(old_mode == got_mode);            // This should be default
    UNITTEST_ASSERT(new_mode == ClaricppBimInt);      // This should be default
    exc(claricpp_backend_set_big_int_mode(old_mode)); // Restore for future tests

    // Test downsizing backend data
    Util::Log::debug("  - downsize");
    UNITTEST_ASSERT(z3_priv.conv_cache_size() != 0);
    exc(claricpp_backend_downsize(z3_manual));
    UNITTEST_ASSERT(z3_priv.conv_cache_size() == 0);

    // Test clearing persistent data
    Util::Log::debug("  - clear_persistent_data");
    (void) z3_cpp->simplify(bv_sym_with_ans.get()); // Populate satd
    UNITTEST_ASSERT(z3_priv.satd_cache_size() != 0);
    exc(claricpp_backend_clear_persistent_data(z3_manual));
    UNITTEST_ASSERT(z3_priv.satd_cache_size() == 0);

    /********************************************************************/
    /*                                Z3                                */
    /********************************************************************/

    Util::Log::debug("Testing Z3 functions");

    // Test creating a z3 backend
    Util::Log::debug("  - new");
    auto z3 { exc(claricpp_backend_z3_new()) };
    auto *const z3_ptr { dynamic_cast<Backend::Z3::Z3 *const>(API::to_cpp(z3).get()) };
    UNITTEST_ASSERT(z3_ptr != nullptr);
    auto &raw_z3 { *z3_ptr };

    // Test creating solvers
    Util::Log::debug("  - new solver");
    const auto solver { exc(claricpp_backend_z3_tls_solver(z3, 0)) };
    UNITTEST_ASSERT(API::to_cpp(solver) != nullptr);
    const auto new_solver { exc(claricpp_backend_z3_new_tls_solver(z3, 0)) };
    UNITTEST_ASSERT(API::to_cpp(new_solver) != nullptr);
    UNITTEST_ASSERT(API::to_cpp(new_solver) != API::to_cpp(solver));
    const auto fst_solver_dup { exc(claricpp_backend_z3_tls_solver(z3, 0)) };
    UNITTEST_ASSERT(API::to_cpp(solver) == API::to_cpp(fst_solver_dup));

    // Prep
    const auto ugeq { [&bv_sym](const UInt i) {
        using C = Mode::Compare;
        return Create::compare<C::Unsigned | C::Greater | C::Eq>(bv_sym, Create::literal(i));
    } };
    const auto raw_uleq { [](const Expr::BasePtr &left, const Expr::BasePtr &right) {
        using C = Mode::Compare;
        return Create::compare<C::Unsigned | C::Less | C::Eq>(left, right);
    } };
    const auto uleq { [&bv_sym, &raw_uleq](const UInt i) {
        return raw_uleq(bv_sym, Create::literal(i));
    } };
    z3::solver &z3_solver { API::to_cpp_ref(solver) };
    const ClaricppExpr ugeq3[] { API::to_c(ugeq(2)), API::to_c(ugeq(3)) }; // NOLINT
    const auto ugeq3_len { 2 };

    // Test add tracked
    Util::Log::debug("  - add tracked");
    [&raw_z3, &z3_solver](auto x) { raw_z3.add(z3_solver, x.get()); }(uleq(0));
    exc(claricpp_backend_z3_add_tracked(z3, solver, API::to_c(ugeq(1))));
    UNITTEST_ASSERT(z3_solver.assertions().size() == 2);
    (void) z3_solver.check(); // Generate unsat_core
    UNITTEST_ASSERT(z3_solver.unsat_core().size() == 1);
    z3_solver.reset();

    [&raw_z3, &z3_solver](auto x) { raw_z3.add(z3_solver, x.get()); }(uleq(0));
    exc(claricpp_backend_z3_add_vec_tracked(z3, solver, ugeq3, 2));
    UNITTEST_ASSERT(z3_solver.assertions().size() == 3);
    (void) z3_solver.check(); // Generate unsat_core
    UNITTEST_ASSERT(z3_solver.unsat_core().size() == 1);
    z3_solver.reset();

    // Test add untracked
    Util::Log::debug("  - add untracked");
    exc(claricpp_backend_z3_add_untracked(z3, solver, API::to_c(ugeq(1))));
    UNITTEST_ASSERT(z3_solver.assertions().size() == 1);
    UNITTEST_ASSERT(z3_solver.unsat_core().empty());
    z3_solver.reset();

    exc(claricpp_backend_z3_add_vec_untracked(z3, solver, ugeq3, 2));
    UNITTEST_ASSERT(z3_solver.assertions().size() == 2);
    UNITTEST_ASSERT(z3_solver.unsat_core().empty());
    z3_solver.reset();

    // Prep
    const auto cl { [](const UInt i) { return API::to_c(Create::literal(i)); } };
    const auto add { [&z3_cpp](z3::solver &s, Expr::BasePtr e) { // NOLINT (copy ok)
        z3_cpp->add<false>(s, e.get());
    } };

    // Test satisfiable
    Util::Log::debug("  - satisfiable");
    add(z3_solver, Create::eq(one, one));
    UNITTEST_ASSERT(exc(claricpp_backend_z3_satisfiable(z3, solver)));
    z3_solver.push();
    add(z3_solver, Create::neq(one, one));
    UNITTEST_ASSERT(!exc(claricpp_backend_z3_satisfiable(z3, solver)));
    z3_solver.pop();
    UNITTEST_ASSERT(exc(claricpp_backend_z3_satisfiable_ec(z3, solver, ugeq3, ugeq3_len)));
    add(z3_solver, Create::eq(bv_sym, one));
    UNITTEST_ASSERT(!exc(claricpp_backend_z3_satisfiable_ec(z3, solver, ugeq3, ugeq3_len)));
    z3_solver.reset();

    // Test solution
    Util::Log::debug("  - solution");
    add(z3_solver, uleq(2));
    const auto bv_sym_c { API::copy_to_c(bv_sym) };
    UNITTEST_ASSERT(exc(claricpp_backend_z3_solution(z3, bv_sym_c, cl(1), solver)));
    UNITTEST_ASSERT(!exc(claricpp_backend_z3_solution(z3, bv_sym_c, cl(3), solver)));
    UNITTEST_ASSERT(
        !exc(claricpp_backend_z3_solution_ec(z3, bv_sym_c, cl(3), solver, ugeq3, ugeq3_len)));
    z3_solver.reset();
    UNITTEST_ASSERT(
        exc(claricpp_backend_z3_solution_ec(z3, bv_sym_c, cl(3), solver, ugeq3, ugeq3_len)));

    // Prep
    const auto sgeq { [&bv_sym](const Int i) {
        using C = Mode::Compare;
        return Create::compare<C::Signed | C::Greater | C::Eq>(
            bv_sym, Create::literal(static_cast<UInt>(i)));
    } };
    const auto sleq { [&bv_sym](const Int i) {
        using C = Mode::Compare;
        return Create::compare<C::Signed | C::Less | C::Eq>(bv_sym,
                                                            Create::literal(static_cast<UInt>(i)));
    } };
    const ClaricppExpr sgeq3[] { API::to_c(sgeq(2)), API::to_c(sgeq(3)) }; // NOLINT
    const auto sgeq3_len { 2 };
    const auto uleq5c { API::to_c(uleq(5)) };
    const auto sleq5c { API::to_c(sleq(5)) };

    // Test min
    Util::Log::debug("  - min");
    add(z3_solver, sgeq(1));
    UNITTEST_ASSERT(exc(claricpp_backend_z3_min_signed(z3, bv_sym_c, solver)) == 1);
    UNITTEST_ASSERT(
        exc(claricpp_backend_z3_min_signed_ec(z3, bv_sym_c, solver, sgeq3, sgeq3_len)) == 3);
    z3_solver.reset();
    add(z3_solver, ugeq(1));
    UNITTEST_ASSERT(exc(claricpp_backend_z3_min_unsigned(z3, bv_sym_c, solver)) == 1);
    UNITTEST_ASSERT(
        exc(claricpp_backend_z3_min_unsigned_ec(z3, bv_sym_c, solver, ugeq3, ugeq3_len)) == 3);

    // Test max
    Util::Log::debug("  - max");
    add(z3_solver, sleq(10));
    UNITTEST_ASSERT(exc(claricpp_backend_z3_max_signed(z3, bv_sym_c, solver)) == 10);
    UNITTEST_ASSERT(exc(claricpp_backend_z3_max_signed_ec(z3, bv_sym_c, solver, &sleq5c, 1)) == 5);
    z3_solver.reset();
    add(z3_solver, uleq(10));
    UNITTEST_ASSERT(exc(claricpp_backend_z3_max_unsigned(z3, bv_sym_c, solver)) == 10);
    UNITTEST_ASSERT(exc(claricpp_backend_z3_max_unsigned_ec(z3, bv_sym_c, solver, &uleq5c, 1)) ==
                    5);

    // Test unsat_core
    Util::Log::debug("  - unsat core");
    z3_cpp->add<true>(z3_solver, bv_neq_bv.get());
    UNITTEST_ASSERT(!exc(claricpp_backend_z3_satisfiable(z3, solver))); // Generate unsat core
    const auto ucore { exc(claricpp_backend_z3_unsat_core(z3, solver)) };
    UNITTEST_ASSERT(ucore.len == 1);
    auto &ucore_0 { API::to_cpp(ucore.arr[0]) }; // NOLINT (not pointer arith)
    UNITTEST_ASSERT(ucore_0 != nullptr);
    UNITTEST_ASSERT(ucore_0->hash == bv_neq_bv->hash);

    // Test eval
    Util::Log::debug("  - eval");
    z3_solver.reset();
    add(z3_solver, uleq(1)); // 0, 1 possible
    // Test n too big
    ARRAY_OUT(ClaricppPrim) evald { exc(claricpp_backend_z3_eval(z3, bv_sym_c, solver, 10)) };
    UNITTEST_ASSERT(evald.len == 2); // Only 0, 1 should have been found
    for (UInt i { 0 }; i < evald.len; ++i) {
        UNITTEST_ASSERT(evald.arr[i].type == ClaricppTypeEnumU64); // NOLINT (not pointer arith)
        UNITTEST_ASSERT(evald.arr[i].data.u64 == i);               // NOLINT (union ok)
    }
    // Test n too small
    evald = exc(claricpp_backend_z3_eval(z3, bv_sym_c, solver, 1));
    UNITTEST_ASSERT(evald.len == 1);

    z3_solver.reset();
    add(z3_solver, uleq(4)); // 0, 1, 2, 3, 4 possible
    // Test n = 2 with constraint >= 3
    evald = exc(claricpp_backend_z3_eval_ec(z3, bv_sym_c, solver, 2, ugeq3, ugeq3_len));
    UNITTEST_ASSERT(evald.len == 2); // Only 3, 4 should have been found
    for (UInt i { 0 }; i < evald.len; ++i) {
        UNITTEST_ASSERT(evald.arr[i].type == ClaricppTypeEnumU64); // NOLINT (not pointer arith)
        UNITTEST_ASSERT(evald.arr[i].data.u64 == 4 - i);           // NOLINT (union ok)
    }

    // Prep
    const auto bv_sym2 { Create::symbol<Expr::BV>("bv_sym2", 64) };
    const ClaricppExpr both_bv_syms[] = { bv_sym_c, API::copy_to_c(bv_sym2) }; // NOLINT
    const auto to_pairs { [](const DOUBLE_ARRAY_OUT(ClaricppPrim) in) {
        std::set<std::pair<UInt, UInt>> ret;
        for (UInt i { 0 }; i < in.len; ++i) {
            const auto a { in.arr[i] }; // NOLINT (not pointer arith)
            UNITTEST_ASSERT(a.len == 2);
            UNITTEST_ASSERT(a.arr[0].type == ClaricppTypeEnumU64); // NOLINT (not pointer arith)
            UNITTEST_ASSERT(a.arr[1].type == ClaricppTypeEnumU64); // NOLINT (not pointer arith)
            ret.insert(std::make_pair(a.arr[0].data.u64, a.arr[1].data.u64)); // NOLINT (union ok)
        }
        return ret;
    } };

    // Test batch eval
    Util::Log::debug("  - batch_eval");
    z3_solver.reset();
    add(z3_solver, uleq(1));
    add(z3_solver, raw_uleq(bv_sym2, Create::literal(UInt(1)))); // 4 solutions
    // Test n too big
    DOUBLE_ARRAY_OUT(ClaricppPrim)
    batch_evald { exc(claricpp_backend_z3_batch_eval(z3, both_bv_syms, 2, solver, 10)) };
    UNITTEST_ASSERT(batch_evald.len == 4); // 4 solutions should be found
    const std::set<std::pair<UInt, UInt>> be_solutions { { 0, 0 }, { 0, 1 }, { 1, 0 }, { 1, 1 } };
    auto eval_got { to_pairs(batch_evald) };
    UNITTEST_ASSERT(be_solutions == eval_got);
    // Test n too small
    batch_evald = exc(claricpp_backend_z3_batch_eval(z3, both_bv_syms, 2, solver, 1));
    UNITTEST_ASSERT(batch_evald.len == 1);
    eval_got = to_pairs(batch_evald);
    UNITTEST_ASSERT(eval_got.size() == 1);
    UNITTEST_ASSERT(be_solutions.find(*eval_got.begin()) != be_solutions.end());

    const auto disjoint_syms_c { API::to_c(Create::neq(bv_sym, bv_sym2)) };
    batch_evald = exc(
        claricpp_backend_z3_batch_eval_ec(z3, both_bv_syms, 2, solver, 10, &disjoint_syms_c, 1));
    UNITTEST_ASSERT(batch_evald.len == 2);
    eval_got = to_pairs(batch_evald);
    const std::set<std::pair<UInt, UInt>> be_solutions_ec { { 0, 1 }, { 1, 0 } };
    UNITTEST_ASSERT(be_solutions_ec == eval_got);

    /********************************************************************/
    /*                             Concrete                             */
    /********************************************************************/
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(backend)
