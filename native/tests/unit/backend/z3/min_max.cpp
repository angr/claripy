/**
 * @file
 * \ingroup unittest
 */
#include "shim_z3.hpp"

#include <testlib/testlib.hpp>


/** Test min / max function */
template <bool Signed, typename T, bool Minimize>
static T get_ext(UnitTest::Friend::ShimZ3 &z3, const Expr::BasePtr &x, const Expr::BasePtr &test_c,
                 const std::vector<Expr::RawPtr> ec = {}) { // NOLINT
    // Get a new solver and add constraint
    const auto solver_ref { z3.bk.template tls_solver<true>() };
    auto &solver { *solver_ref };
    z3.bk.add(solver, test_c.get());
    // Min / max functions
    auto f { [&z3](auto &&...args) {
        return Minimize ? z3.bk.min<Signed>(args...) : z3.bk.max<Signed>(args...);
    } };
    auto f_ec { [&z3](auto &&...args) {
        return Minimize ? z3.bk.min<Signed>(args...) : z3.bk.max<Signed>(args...);
    } };
    // Call the min / max function
    return static_cast<T>(ec.empty() ? f(x.get(), solver) : f_ec(x.get(), solver, ec));
}

/** Tests min and maxed for the chosen type */
template <typename T, bool Signed = std::is_signed_v<T>>
static void min_max_test(UnitTest::Friend::ShimZ3 &z3) {
    static_assert(std::is_integral_v<T>, "T must be an integral type");
    Util::Log::debug("\t- Signed: ", std::boolalpha, Signed);

    // For brevity
    namespace C = Create;
    namespace E = Expr; // NOLINT (false positive)
    using EC = std::vector<E::RawPtr>;

    // Prep
    const auto unsign { Util::unsign<T, true> };
    const auto int_max { std::numeric_limits<T>::max() };
    const auto int_min { std::numeric_limits<T>::min() };

    // x and expr generators
    const auto x { C::symbol_bv("x", CHAR_BIT * sizeof(T)) };
    const auto num { [&unsign](const T v) { return C::literal(unsign(T { v })); } };
    const auto neq { [&x, &unsign](const T y) { return C::neq(x, C::literal(unsign(y))); } };

    // Exprs
    const auto xleq10 { (Signed ? C::slt : C::ult)(x, num(10), {}) };
    const auto xleq5 { (Signed ? C::slt : C::ult)(x, num(5), {}) };
    const auto xgeq5 { (Signed ? C::sgt : C::ugt)(x, num(5), {}) };

    const auto plus1 { C::and_({ xleq5, neq(int_min) }) };
    const auto plus2 { C::and_({ xleq5, neq(int_min), neq(int_min + 1) }) };
    const auto minus1 { C::and_({ xgeq5, neq(int_max) }) };
    const auto minus2 { C::and_({ xgeq5, neq(int_max), neq(int_max - 1) }) };

    const auto max { C::eq(x, Create::literal(unsign(int_max))) };
    const auto min { C::eq(x, Create::literal(unsign(int_min))) };

    // Test functions
    const auto get_min { [&z3, &x](auto e) {
        return get_ext<Signed, T, true>(z3, x, std::move(e));
    } };
    const auto get_max { [&z3, &x](auto e) {
        return get_ext<Signed, T, false>(z3, x, std::move(e));
    } };

    // Test bounds

    // Test x > 5
    UNITTEST_ASSERT(get_min(xgeq5) == 6);
    UNITTEST_ASSERT(get_max(xgeq5) == int_max);

    // Test x < 5
    UNITTEST_ASSERT(get_min(xleq5) == int_min);
    UNITTEST_ASSERT(get_max(xleq5) == 4);

    // Test extra constraints

    // Test x < 10; ec: x > 5
    Util::Log::debug("\t\t- Extra constraints tests...");
    T res { get_ext<Signed, T, true>(z3, x, xleq10, EC { xgeq5.get() }) };
    UNITTEST_ASSERT(res == 6);

    // Test x > 5; ec: x < 10
    res = get_ext<Signed, T, false>(z3, x, xgeq5, EC { xleq10.get() });
    UNITTEST_ASSERT(res == 9);

    // Test near extrema; i.e. last step of binary search

    // Test x < 5 && x != int_min
    Util::Log::debug("\t\t- Testing final step...");
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
    Util::Log::debug("\t\t- Testing extrema...");
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
template <bool Signed> static void min_max_t(UnitTest::Friend::ShimZ3 &z3) {
    min_max_test<Wrap<Signed, I64>>(z3);
    min_max_test<Wrap<Signed, int32_t>>(z3);
    min_max_test<Wrap<Signed, int16_t>>(z3);
    min_max_test<Wrap<Signed, int8_t>>(z3);
}

/** Test the backend min and max functions */
void min_max() {
    UnitTest::Friend::ShimZ3 z3;
    min_max_t<true>(z3);
    z3.bk.downsize(); // Prevent FNV1a hash collisions; @todo Improve hash algorithm
    min_max_t<false>(z3);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(min_max)
