/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Test add */
void add() {
    namespace Ex = Expression;

    auto z3 { Backend::Z3::Z3 {} };
    auto solver_ref { z3.tls_solver() };
    auto &solver { *solver_ref };

    // Constraints
    const auto x { Create::symbol<Ex::BV>("x", 64) };
    const uint64_t umax { std::numeric_limits<uint64_t>::max() };
    auto x_not_max { Create::neq<Ex::BV>(x, Create::literal(umax)) };

    // Desired output string components
    const std::string prefix { "(declare-fun x () (_ BitVec 64))\n" };
    const std::string distinct { "(distinct x #xffffffffffffffff)" };
    const std::string assert_distinct { "(assert " + distinct + ")\n" };

    // Add a constraint twice
    z3.add<false>(solver, x_not_max.get());
    z3.add<false>(solver, x_not_max.get());

    // Verify the solvers lines
    std::stringstream is;
    is << solver;
    UNITTEST_ASSERT(is.str() == prefix + assert_distinct + assert_distinct)

    // Add tracked constraints twice
    solver.reset();
    z3.add<true>(solver, x_not_max.get());
    z3.add<true>(solver, x_not_max.get());

    // Verify solver lines
    is.str("");
    is << solver;
    const std::string bool_name { '|' + std::to_string(x_not_max->hash) + '|' };
    UNITTEST_ASSERT(is.str() == prefix + "(declare-fun " + bool_name + " () Bool)\n(assert (=> " +
                                    bool_name + ' ' + distinct + "))\n");
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(add)
