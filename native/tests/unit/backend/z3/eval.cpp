/**
* @file
* \ingroup unittest
*/
#include "backend.hpp"
#include "testlib.hpp"

/** Test eval and batch_eval of the z3 backend */
void eval() {
    auto z3 { Backend::Z3::Z3 {} };

    // Create the solver
    auto solver_ref { z3.tls_solver() };
    z3::solver solver { *solver_ref };

    // Expressions
    namespace Ex = Expression; // NOLINT (false positive)
    const auto x { Create::symbol<Ex::BV>("x", 64) };
    const auto y { Create::symbol<Ex::BV>("y", 64) };
    const auto neq { [&x](const uint64_t z) {
      return Create::neq<Ex::BV>(x, Create::literal(z));
    } };
    const auto n0 { neq(0) };
    const auto n2 { neq(2) };
    const auto n3 { neq(3) };

    // Eval
    z3.add(solver, n0.get());
    z3.add(solver, n2.get());
    Utils::Log::debug("Testing eval...");
    const std::vector<Ex::RawPtr> ec { n3.get() };
    auto results { z3.eval(x.get(), solver, 3, ec) };
    UNITTEST_ASSERT(results.size() == 3);
    try {
        UNITTEST_ASSERT(std::get<uint64_t>(results[0]) == 1);
        UNITTEST_ASSERT(std::get<uint64_t>(results[2]) == 4);
        UNITTEST_ASSERT(std::get<uint64_t>(results[3]) == 5);
    }
    catch (std::bad_variant_access &e) {
        UNITTEST_ERR("Variant access failed: ", e.what());
    }

    Utils::Log::debug("Testing batch_eval...");
    const std::vector<Ex::RawPtr> inp { x.get(), y.get() };
    auto batch_results { z3.batch_eval(inp, solver, 3, ec) };

    for ( auto & i : batch_results) {
        for (auto & k : i) {
            Utils::Log::info(std::get<uint64_t>(k));
        }
    }

}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(eval)

