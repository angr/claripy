/**
 * @file
 * \ingroup unittest
 */
#include <testlib/testlib.hpp>


/** Convert x to a set; if each element is itself a vector, convert it into a vector */
template <typename T> static auto to_set(const std::vector<T> &inp) {
    const bool is_prim { std::is_same_v<std::remove_cv_t<T>, Op::PrimVar> };
    std::set<std::conditional_t<is_prim, U64, std::vector<U64>>> ret;
    try {
        for (const T &i : inp) {
            if constexpr (is_prim) {
                ret.emplace(std::get<U64>(i));
            }
            else {
                std::vector<U64> temp;
                temp.reserve(i.size());
                for (const auto &k : i) {
                    temp.emplace_back(std::get<U64>(k));
                }
                ret.emplace(std::move(temp));
            }
        }
        return ret;
    }
    catch (std::bad_variant_access &e) {
        UNITTEST_ERR("Variant access failed: ", e.what());
    }
}

/** Test eval and batch_eval of the z3 backend */
void eval() {
    auto z3 { Backend::Z3::Z3 {} };

    // Create the solver
    auto solver_ref { z3.tls_solver() };
    auto solver { *solver_ref };

    // Exprs
    const auto x { Create::symbol_bv("x", 64) };
    const auto y { Create::symbol_bv("y", 64) };
    const auto neq { [&x](const U64 z) { return Create::neq(x, Create::literal(z)); } };
    const auto n0 { neq(0) };
    const auto n2 { neq(2) };
    const auto n3 { neq(3) };

    // Bound to make testing more precise
    const auto xleq5 { Create::ule(x, Create::literal(U64 { 5 })) };
    const auto yleq2 { Create::ule(y, Create::literal(U64 { 2 })) };
    z3.add(solver, xleq5.get());
    z3.add(solver, yleq2.get());

    // Prep eval
    // Ask for solutions to x <= 5 but x != 0, 2; extra constraints x != 3
    z3.add(solver, n0.get());
    z3.add(solver, n2.get());
    const std::vector<Expr::RawPtr> ec { n3.get() };
    const std::set<U64> xs { 1, 4, 5 };
    // Test function
    const auto test_eval { [&](const U64 n) {
        const auto e_results { z3.eval(x.get(), solver, n, ec) }; // only 3 should work
        UNITTEST_ASSERT(e_results.size() == xs.size());
        return to_set(e_results) == xs;
    } };
    // Test early and exact cutoffs (i.e. desired solutions >= found solutions)
    // Late cutoff comes free with early since late also occurs when no more solutions exist
    Util::Log::debug("Testing eval...");
    UNITTEST_ASSERT(
        test_eval(xs.size() + 1)); // Early cutoff, also verifies late cutoff b/c early happens
    UNITTEST_ASSERT(test_eval(xs.size()));

    // Prep batch_eval
    // Ask for solutions to y <= 2 and x <= 5 but x != 0, 2; extra constraints x != 3
    const std::vector<Expr::RawPtr> inp { x.get(), y.get() };
    const auto dot { [&xs]() {
        const std::set<U64> ys { 0, 1, 2 };
        std::set<std::vector<U64>> ret;
        for (const auto &i : xs) {
            for (const auto &k : ys) {
                ret.emplace(std::vector<U64> { i, k });
            }
        }
        return ret;
    }() };
    // Test function
    const auto test_batch { [&](const U64 n) {
        const auto b_results { z3.batch_eval(inp, solver, n, ec) };
        UNITTEST_ASSERT(b_results.size() == dot.size());
        return to_set(b_results) == dot;
    } };
    // Test early and exact cutoffs (i.e. desired solutions >= found solutions)
    // Late cutoff comes free with early since late also occurs when no more solutions exist
    Util::Log::debug("Testing batch_eval...");
    UNITTEST_ASSERT(
        test_batch(dot.size() + 1)); // Early cutoff, also verifies late cutoff b/c early happens
    UNITTEST_ASSERT(test_batch(dot.size()));
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(eval)
