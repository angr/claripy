/**
 * @file
 * \ingroup unittest
 */
#include "backend.hpp"
#include "testlib.hpp"


template <typename T, bool Signed = std::is_signed_v<T>>
static void min_max_sign_t(Backend::Z3::Z3 &z3) {
    static_assert(std::is_integral_v<T>, "T must be an integral type");
    Utils::Log::debug("\tSigned: ", std::boolalpha, Signed);
    z3.downsize(); // To avoid hash collisions of FNV1a @todo : make hashing better

    // For brevity
    namespace C = Create;
    using M = Mode::Compare;
    namespace E = Expression; // NOLINT (false positive)

    // Prep
    const auto x { C::symbol<E::BV>("x", C_CHAR_BIT * sizeof(T)) };
    const auto &unsign { Utils::unsign<T, true> };
    const auto five { C::literal(unsign(T { 5 })) };

    // Test function
    const auto get_min { [&x, &z3](E::BasePtr e) {
        const auto solver { z3.new_tls_solver() };
        solver->add(z3.convert(e));
        auto s { *solver.get() };
        return static_cast<T>(z3.min<Signed>(z3.convert(x), s));
    } };

    // Test x > 5
    T min { get_min(C::compare<E::BV, M::Greater | M::Neq | M::Signed>(x, five)) };
    UNITTEST_ASSERT_MSG(min == 6, "min: ", min);

    // Test x < 5
    const auto xleq5 { C::compare<E::BV, M::Less | M::Neq | M::Signed>(x, five) };
    const auto int_min { std::numeric_limits<T>::min() };
    min = get_min(xleq5);
    UNITTEST_ASSERT_MSG(min == int_min, "min: ", min);

    // Test x < 5 && x != int_min
    const auto neq { [&x](const T y) { return C::neq<E::BV>(x, C::literal(unsign(y))); } };
    const auto plus1 { C::and_<E::Bool>({ xleq5, neq(int_min) }) };
    min = get_min(plus1);
    UNITTEST_ASSERT_MSG(min == int_min + 1, "min: ", min);

    // Test x < 5 && x != int_min && x != int_min+1
    const auto plus2 { C::and_<E::Bool>({ xleq5, neq(int_min), neq(int_min + 1) }) };
    min = get_min(plus2);
    UNITTEST_ASSERT_MSG(min == int_min + 2, "min: ", min);

    // Test x == int_max
    const auto int_max { std::numeric_limits<T>::max() };
    const auto max { C::eq<E::BV>(x, Create::literal(unsign(int_max))) };
    min = get_min(max);
    UNITTEST_ASSERT_MSG(min == int_max, "min: ", min);
}

template <typename T> static void min_max_t(Backend::Z3::Z3 &z3) {
    static_assert(std::is_integral_v<T>, "T must be integral");
    min_max_sign_t<std::make_signed_t<T>>(z3);
    min_max_sign_t<std::make_unsigned_t<T>>(z3);
}

/** Test the backend min and max functions
 * @todo: max
 */
void min_max() {
    auto z3 { Backend::Z3::Z3 {} };
    min_max_t<int64_t>(z3);
    //    min_max_t<int32_t>(z3);
    //    min_max_t<int16_t>(z3);
    //    min_max_t<int8_t>(z3);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(min_max)