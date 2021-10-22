/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Used to try to get valid expr and op pointers */
template <typename E, typename O> static auto get_pointers(const ClaricppExpr in) {
    const Expr::RawPtr exp { API::to_cpp_ref(in).get() };
    UNITTEST_ASSERT(exp != nullptr);
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
    namespace Ex = Expr;

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
    symbol<Ex::Bool>(claricpp_create_symbol_bool(name, { nullptr }), name, 0);
    symbol<Ex::String>(claricpp_create_symbol_string(name, bl, { nullptr }), name, bl);
    symbol<Ex::VS>(claricpp_create_symbol_vs(name, bl, { nullptr }), name, bl);
    symbol<Ex::FP>(claricpp_create_symbol_fp(name, bl, { nullptr }), name, bl);
    symbol<Ex::BV>(claricpp_create_symbol_bv(name, bl, { nullptr }), name, bl);

    // Literal
    Util::Log::debug("Testing literal creation functions...");
    literal<Ex::Bool, bool>(claricpp_create_literal_bool(true, { nullptr }), true, 0);
    literal<Ex::String, std::string>(claricpp_create_literal_string(name, { nullptr }), name,
                                     std::strlen(name) * C_CHAR_BIT);
    literal<Ex::FP, float>(claricpp_create_literal_fp_float(3.f, { nullptr }), 3.f, 32); // NOLINT
    literal<Ex::FP, double>(claricpp_create_literal_fp_double(3., { nullptr }), 3., 64); // NOLINT
    literal<Ex::VS, PyObj::VSPtr>(claricpp_create_literal_vs(1, 2, n, { nullptr }), pyobj, n);
    literal<Ex::BV, uint8_t>(claricpp_create_literal_bv_u8(n, { nullptr }), n, 8);    // NOLINT
    literal<Ex::BV, uint16_t>(claricpp_create_literal_bv_u16(n, { nullptr }), n, 16); // NOLINT
    literal<Ex::BV, uint32_t>(claricpp_create_literal_bv_u32(n, { nullptr }), n, 32); // NOLINT
    literal<Ex::BV, uint64_t>(claricpp_create_literal_bv_u64(n, { nullptr }), n, 64); // NOLINT
    literal<Ex::BV, BigInt>(claricpp_create_literal_bv_big_int_mode_str("10", n, { nullptr }),
                            BigInt { "10", n }, n);
    literal<Ex::BV, BigInt>(claricpp_create_literal_bv_big_int_mode_int("10", n, { nullptr }),
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

#define UNARY(NAME, FUN, TYPE, OTHER)                                                             \
    Util::Log::debug("Testing " #NAME "...");                                                     \
    const auto FUN { claricpp_create_##NAME(API::copy_to_c(TYPE##_sym), { nullptr }) };           \
    UNITTEST_ASSERT(API::to_cpp_ref(FUN)->hash == Create::FUN(TYPE##_sym)->hash);                 \
    UNITTEST_ASSERT(API::to_cpp_ref(FUN)->hash != Create::FUN(TYPE##_##OTHER)->hash)

    UNARY(abs, abs, fp, 64);
    UNARY(neg, neg, bv, 64);
    UNARY(not, not_, bool, true);
    UNARY(invert, invert, bv, 64);
    UNARY(reverse, reverse, bv, 64);

// Cleanup
#undef UNARY

    // String

    // FP
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(create)
