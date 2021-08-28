/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


/** Test min / max function */
template <bool Signed, typename T, bool Minimize>
static T get_ext(Backend::Z3::Z3 &z3, const Expression::BasePtr &x,
                 const Expression::BasePtr &test_c,
                 const std::vector<Expression::BasePtr> ec = {}) { // NOLINT
    // Get a solver and add constraint
    const auto solver_ref { z3.tls_solver() };
    auto &solver { *solver_ref };
    z3.add(solver, test_c.get());
    // Min / max functions
    auto f { [&z3](auto &&...args) {
        return Minimize ? z3.min<Signed>(args...) : z3.max<Signed>(args...);
    } };
    auto f_ec { [&z3](auto &&...args) {
        return Minimize ? z3.min<Signed>(args...) : z3.max<Signed>(args...);
    } };
    // Call the min / max function
    const auto conv { z3.convert(x) };
    return static_cast<T>(ec.empty() ? f(conv, solver) : f_ec(conv, solver, ec));
}

/** Tests min and maxed for the chosen type */
template <typename T, bool Signed = std::is_signed_v<T>>
static void min_max_test(Backend::Z3::Z3 &z3) {
    static_assert(std::is_integral_v<T>, "T must be an integral type");
    Utils::Log::debug("\t- Signed: ", std::boolalpha, Signed);

    // For brevity
    namespace C = Create;
    using M = Mode::Compare;
    namespace E = Expression; // NOLINT (false positive)
    using EC = std::vector<E::BasePtr>;

    // Prep
    const auto unsign { Utils::unsign<T, true> };
    const auto int_max { std::numeric_limits<T>::max() };
    const auto int_min { std::numeric_limits<T>::min() };
    const constexpr M neq_mask { M::Neq | (Signed ? M::Signed : M::Unsigned) };

    // x and expr generators
    const auto x { C::symbol<E::BV>("x", C_CHAR_BIT * sizeof(T)) };
    const auto num { [&unsign](const T v) { return C::literal(unsign(T { v })); } };
    const auto neq { [&x, &unsign](const T y) {
        return C::neq<E::BV>(x, C::literal(unsign(y)));
    } };

    // Exprs
    const auto xleq10 { C::compare<E::BV, M::Less | neq_mask>(x, num(10)) };
    const auto xleq5 { C::compare<E::BV, M::Less | neq_mask>(x, num(5)) };
    const auto xgeq5 { C::compare<E::BV, M::Greater | neq_mask>(x, num(5)) };

    const auto plus1 { C::and_<E::Bool>({ xleq5, neq(int_min) }) };
    const auto plus2 { C::and_<E::Bool>({ xleq5, neq(int_min), neq(int_min + 1) }) };
    const auto minus1 { C::and_<E::Bool>({ xgeq5, neq(int_max) }) };
    const auto minus2 { C::and_<E::Bool>({ xgeq5, neq(int_max), neq(int_max - 1) }) };

    const auto max { C::eq<E::BV>(x, Create::literal(unsign(int_max))) };
    const auto min { C::eq<E::BV>(x, Create::literal(unsign(int_min))) };

    // Test functions
    const auto get_min { [&z3, &x](auto e) {
        return get_ext<Signed, T, true>(z3, x, std::move(e));
    } };
    const auto get_max { [&z3, &x](auto e) {
        return get_ext<Signed, T, false>(z3, x, std::move(e));
    } };

    // Test bounds

    // Test x > 5
    Utils::Log::debug("\t\t- Standard tests...");
    UNITTEST_ASSERT(get_min(xgeq5) == 6);
    UNITTEST_ASSERT(get_max(xgeq5) == int_max);

    // Test x < 5
    UNITTEST_ASSERT(get_min(xleq5) == int_min);
    UNITTEST_ASSERT(get_max(xleq5) == 4);

    // Test extra constraints

    // Test x < 10; ec: x > 5
    Utils::Log::debug("\t\t- Extra constraints tests...");
    T res { get_ext<Signed, T, true>(z3, x, xleq10, EC { xgeq5 }) };
    UNITTEST_ASSERT(res == 6);

    // Test x > 5; ec: x < 10
    res = get_ext<Signed, T, false>(z3, x, xgeq5, EC { xleq10 });
    UNITTEST_ASSERT(res == 9);

    // Test near extrema; i.e. last step of binary search

    // Test x < 5 && x != int_min
    Utils::Log::debug("\t\t- Testing final step...");
    UNITTEST_ASSERT(get_min(plus1) == int_min + 1);
    UNITTEST_ASSERT(get_max(plus1) == 4);

    // Test x < 5 && x != int_min && x != int_min+1
    UNITTEST_ASSERT(get_min(plus2) == int_min + 2);
    UNITTEST_ASSERT(get_max(plus2) == 4);

    // Test x > 5 && x != int_max
    UNITTEST_ASSERT(get_max(minus1) == int_max - 1);
    UNITTEST_ASSERT(get_min(minus1) == 6);

    // Test x > 5 && x != int_max && x != int_max-1
    UNITTEST_ASSERT(get_max(minus2) == int_max - 2);
    UNITTEST_ASSERT(get_min(minus2) == 6);

    // Test tight extrema

    // Test x == int_max
    Utils::Log::debug("\t\t- Testing extrema...");
    UNITTEST_ASSERT(get_min(max) == int_max);
    UNITTEST_ASSERT(get_max(max) == int_max);

    // Test x == int_min
    UNITTEST_ASSERT(get_min(min) == int_min);
    UNITTEST_ASSERT(get_max(min) == int_min);
}

/** Returns a T that is signed / unsigned depending on Signed */
template <bool Signed, typename T>
using Wrap = std::conditional_t<Signed, std::make_signed_t<T>, std::make_unsigned_t<T>>;

/** Tests min and max for the chosen sign */
template <bool Signed> static void min_max_t(Backend::Z3::Z3 &z3) {
    min_max_test<Wrap<Signed, int64_t>>(z3);
    min_max_test<Wrap<Signed, int32_t>>(z3);
    min_max_test<Wrap<Signed, int16_t>>(z3);
    min_max_test<Wrap<Signed, int8_t>>(z3);
}

/** Test the backend min and max functions */
void min_max() {
    auto z3 { Backend::Z3::Z3 {} };
    min_max_t<true>(z3);
    z3.downsize(); // Prevent FNV1a hash collisions; @todo Improve hash algorithm
    min_max_t<false>(z3);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(min_max)
