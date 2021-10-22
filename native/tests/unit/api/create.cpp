/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Used to try to get valid expr and op pointers */
template <typename E, typename O> static auto get_pointers(const ClaricppExpr in) {
    const Expr::RawPtr exp { API::to_cpp_ref(in).get() };
    UNITTEST_ASSERT(exp != nullptr)
    CTSC<E> cast { dynamic_cast<CTSC<E>>(exp) };
    UNITTEST_ASSERT(cast != nullptr);
    CTSC<O> lit { dynamic_cast<CTSC<O>>(cast->op.get()) };
    UNITTEST_ASSERT(lit != nullptr);
    return std::make_pair(cast, lit);
}

/** Used to verify the symbols API
 *  bit_length is checked if T is not a Bool
 */
template <typename T>
static void symbol(const ClaricppExpr in, PyStr name, const SIZE_T bit_length) {
    const auto [expr, op] { get_pointers<T, Op::Symbol>(in) };
    UNITTEST_ASSERT(op->name == name);
    if constexpr (!std::is_same_v<T, Expr::Bool>) {
        UNITTEST_ASSERT(expr->bit_length == bit_length);
    }
    (void) bit_length;
}

/** Used to verify the literals API
 *  bit_length is checked if T is not a Bool
 */
template <typename T, typename Val>
static void literal(const ClaricppExpr in, const Val value, const SIZE_T bit_length) {
    const auto [expr, op] { get_pointers<T, Op::Literal>(in) };
    UNITTEST_ASSERT(std::holds_alternative<Val>(op->value));
    if constexpr (std::is_same_v<PyObj::VSPtr, Val>) {
        UNITTEST_ASSERT(std::get<Val>(op->value)->hash == value->hash);
    }
    else {
        UNITTEST_ASSERT(std::get<Val>(op->value) == value);
    }
    if constexpr (!std::is_same_v<T, Expr::Bool>) {
        UNITTEST_ASSERT(expr->bit_length == bit_length);
    }
    (void) bit_length;
}

/** Verify the Create API works
 * @todo test spav
 */
void create() {

    // Constants
    const char name[] { "name" };
    const SIZE_T bl { 64_ui };
    const uint8_t n { 8 };

    // Non-trivial constants
    const auto pyobj { std::make_shared<PyObj::VS>(1, 2, 3) };
    const auto bool_sym { Create::symbol("test") };
    const auto bool_true { Create::literal(true) };
    const auto bv_sym { Create::symbol<Expr::BV>("bv", 64) };
    const auto fp_sym { Create::symbol<Expr::FP>("fp", 64) };
    const auto bv_64 { Create::literal(UInt { 64 }) };
    const auto fp_64 { Create::literal(64.) };

    // Symbol
    Util::Log::debug("Testing symbol creation functions...");
    symbol<Expr::Bool>(claricpp_create_symbol_bool(name, { nullptr }), name, 0);
    symbol<Expr::String>(claricpp_create_symbol_string(name, bl, { nullptr }), name, bl);
    symbol<Expr::VS>(claricpp_create_symbol_vs(name, bl, { nullptr }), name, bl);
    symbol<Expr::FP>(claricpp_create_symbol_fp(name, bl, { nullptr }), name, bl);
    symbol<Expr::BV>(claricpp_create_symbol_bv(name, bl, { nullptr }), name, bl);

    // Literal
    Util::Log::debug("Testing literal creation functions...");
    literal<Expr::Bool, bool>(claricpp_create_literal_bool(true, { nullptr }), true, 0);
    literal<Expr::String, std::string>(claricpp_create_literal_string(name, { nullptr }), name,
                                       std::strlen(name) * C_CHAR_BIT);
    literal<Expr::FP, float>(claricpp_create_literal_fp_float(3.f, { nullptr }), 3.f,
                             32); // NOLINT
    literal<Expr::FP, double>(claricpp_create_literal_fp_double(3., { nullptr }), 3.,
                              64); // NOLINT
    literal<Expr::VS, PyObj::VSPtr>(claricpp_create_literal_vs(1, 2, n, { nullptr }), pyobj, n);
    literal<Expr::BV, uint8_t>(claricpp_create_literal_bv_u8(n, { nullptr }), n, 8);    // NOLINT
    literal<Expr::BV, uint16_t>(claricpp_create_literal_bv_u16(n, { nullptr }), n, 16); // NOLINT
    literal<Expr::BV, uint32_t>(claricpp_create_literal_bv_u32(n, { nullptr }), n, 32); // NOLINT
    literal<Expr::BV, uint64_t>(claricpp_create_literal_bv_u64(n, { nullptr }), n, 64); // NOLINT
    literal<Expr::BV, BigInt>(claricpp_create_literal_bv_big_int_mode_str("10", n, { nullptr }),
                              BigInt { "10", n }, n);
    literal<Expr::BV, BigInt>(claricpp_create_literal_bv_big_int_mode_int("10", n, { nullptr }),
                              BigInt { 10, n }, n);

    // Non-Trivial

    Util::Log::debug("Testing extract...");
    const auto extract { claricpp_create_extract(2, 1, API::copy_to_c(bv_sym), { nullptr }) };
    UNITTEST_ASSERT(API::to_cpp_ref(extract)->hash == Create::extract(2, 1, bv_sym)->hash);
    UNITTEST_ASSERT(API::to_cpp_ref(extract)->hash != Create::extract(1, 0, bv_sym)->hash);

    Util::Log::debug("Testing if...");
    const auto if_ { claricpp_create_if(API::copy_to_c(bool_sym), API::copy_to_c(bv_sym),
                                        API::copy_to_c(bv_64), { nullptr }) };
    UNITTEST_ASSERT(API::to_cpp_ref(if_)->hash == Create::if_(bool_sym, bv_sym, bv_64)->hash);
    UNITTEST_ASSERT(API::to_cpp_ref(if_)->hash != Create::if_(bool_sym, bv_64, bv_64)->hash);

    // Trivial Unary

/** A local macro used for testing */
#define UNARY(NAME, FUN, TYPE, OTHER)                                                              \
    Util::Log::debug("Testing " #NAME "...");                                                      \
    const auto FUN { claricpp_create_##NAME(API::copy_to_c(TYPE##_sym), { nullptr }) };            \
    UNITTEST_ASSERT(API::to_cpp_ref(FUN)->hash == Create::FUN(TYPE##_sym)->hash);                  \
    UNITTEST_ASSERT(API::to_cpp_ref(FUN)->hash != Create::FUN(TYPE##_##OTHER)->hash)

    UNARY(abs, abs, fp, 64);
    UNARY(neg, neg, bv, 64);
    UNARY(not, not_, bool, true);
    UNARY(invert, invert, bv, 64);
    UNARY(reverse, reverse, bv, 64);

// Cleanup
#undef UNARY

/** A local macro used for testing */
#define UINT_BINARY(FUN)                                                                           \
    Util::Log::debug("Testing " #FUN "...");                                                       \
    const auto FUN { claricpp_create_##FUN(API::copy_to_c(bv_sym), 4, { nullptr }) };              \
    UNITTEST_ASSERT(API::to_cpp_ref(FUN)->hash == Create::FUN(bv_sym, 4)->hash);                   \
    UNITTEST_ASSERT(API::to_cpp_ref(FUN)->hash != Create::FUN(bv_sym, 5)->hash)

    UINT_BINARY(sign_ext);
    UINT_BINARY(zero_ext);

// Cleanup
#undef UINT_BINARY

/** A local macro used for testing */
#define BINARY(FUN, ARG, REAL_FUN)                                                                 \
    Util::Log::debug("Testing " #FUN "...");                                                       \
    const auto FUN##_test { claricpp_create_##FUN(API::copy_to_c(ARG), API::copy_to_c(ARG),        \
                                                  { nullptr }) };                                  \
    UNITTEST_ASSERT(API::to_cpp_ref(FUN##_test)->hash == REAL_FUN(ARG, ARG)->hash);

    // Comparisons
    using C = Mode::Compare;
    BINARY(eq, bv_64, Create::eq);
    BINARY(neq, bv_64, Create::neq);
    BINARY(slt, bv_64, Create::compare<C::Signed | C::Less | C::Neq>);
    BINARY(sle, bv_64, Create::compare<C::Signed | C::Less | C::Eq>);
    BINARY(sgt, bv_64, Create::compare<C::Signed | C::Greater | C::Neq>);
    BINARY(sge, bv_64, Create::compare<C::Signed | C::Greater | C::Eq>);
    BINARY(ult, bv_64, Create::compare<C::Unsigned | C::Less | C::Neq>);
    BINARY(ule, bv_64, Create::compare<C::Unsigned | C::Less | C::Eq>);
    BINARY(ugt, bv_64, Create::compare<C::Unsigned | C::Greater | C::Neq>);
    BINARY(uge, bv_64, Create::compare<C::Unsigned | C::Greater | C::Eq>);

    // Math
    BINARY(sub, bv_64, Create::sub);
    BINARY(sdiv, bv_64, Create::div<true>);
    BINARY(udiv, bv_64, Create::div<false>);
    BINARY(smod, bv_64, Create::mod<true>);
    BINARY(umod, bv_64, Create::mod<false>);

    // String

    // FP
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(create)
