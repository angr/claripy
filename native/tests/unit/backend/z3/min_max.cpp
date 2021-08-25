/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"

/** Test the backend min and max functions
 * @todo: max
 */
void min_max() {
    z3::context ctx;
    auto z3 { Backend::Z3::Z3 {} };

    // For brevity
    namespace C = Create;
    using M = Mode::Compare;
    namespace E = Expression;

    // Prep
    const auto x { C::symbol<E::BV>("x", 64) };
    const auto mfive { C::literal(-5_ui) };

    // Test funciton
    const auto get_min { [&x, &z3](Expression::BasePtr e) {
        const auto solver { z3.new_tls_solver() };
        solver->add(z3.convert(e));
        auto s { *solver.get() };
        return z3.min<true>(z3.convert(x), s);
    } };

    // Test x > -5
    auto min { get_min(C::compare<E::BV, M::Greater | M::Neq | M::Signed>(x, mfive)) };
    UNITTEST_ASSERT(min == -5 + 1);

    // Test x < -5
    const auto xleq5 { C::compare<E::BV, M::Less | M::Neq | M::Signed>(x, mfive) };
    const auto int_min { std::numeric_limits<int64_t>::min() };
    UNITTEST_ASSERT(get_min(xleq5) == int_min);

    // Test x < -5 && x != uint_min
    const auto neq { [&x](const int64_t y) {
        return C::neq<E::BV>(x, C::literal(Utils::unsign(y)));
    } };
    const auto plus1 { C::and_<E::Bool>({ xleq5, neq(int_min) }) };
    UNITTEST_ASSERT(get_min(plus1) == int_min + 1);

    // Test x < -5 && x != uint_min && x != uint_min+1
    const auto plus2 { C::and_<E::Bool>({ xleq5, neq(int_min), neq(int_min + 1) }) };
    UNITTEST_ASSERT(get_min(plus2) == int_min + 2);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(min_max)