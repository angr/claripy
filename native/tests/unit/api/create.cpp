/**
 * @file
 * \ingroup unittest
 */
#include "testlib.hpp"


/** Used to try to get valid expr and op pointers */
template <typename E, typename O> static auto get_pointers(Constants::CTSC<ClaricppExpr> in) {
    const Expression::RawPtr exp { in->ptr.get() };
    UNITTEST_ASSERT(exp != nullptr);
    Constants::CTSC<E> cast { dynamic_cast<Constants::CTSC<E>>(exp) };
    UNITTEST_ASSERT(cast != nullptr);
    Constants::CTSC<O> lit { dynamic_cast<Constants::CTSC<O>>(cast->op.get()) };
    UNITTEST_ASSERT(lit != nullptr);
    return std::make_pair(cast, lit);
}

/** Used to verify the symbols API
 *  bit_length is checked if T is not a Bool
 */
template <typename T>
static void symbol(Constants::CTSC<ClaricppExpr> in, PyStr name, const SIZE_T bit_length) {
    const auto [expr, op] { get_pointers<T, Op::Symbol>(in) };
    UNITTEST_ASSERT(op->name == name);
    if constexpr (!std::is_same_v<T, Expression::Bool>) {
        UNITTEST_ASSERT(expr->bit_length == bit_length);
    }
    (void) bit_length;
}

/** Used to verify the literals API
 *  bit_length is checked if T is not a Bool
 */
template <typename T, typename Val>
static void literal(Constants::CTSC<ClaricppExpr> in, const Val value, const SIZE_T bit_length) {
    const auto [expr, op] { get_pointers<T, Op::Literal>(in) };
    UNITTEST_ASSERT(std::holds_alternative<Val>(op->value));
    if constexpr (std::is_same_v<PyObj::VSPtr, Val>) {
        UNITTEST_ASSERT(std::get<Val>(op->value)->hash == value->hash);
    }
    else {
        UNITTEST_ASSERT(std::get<Val>(op->value) == value);
    }
    if constexpr (!std::is_same_v<T, Expression::Bool>) {
        UNITTEST_ASSERT(expr->bit_length == bit_length);
    }
    (void) bit_length;
}

/** Verify the Create API works */
void create() {
    namespace Ex = Expression;

    // Constants
    const char name[] { "name" };
    const SIZE_T bl { 64_ui };
    const uint8_t n { 8 };
    const auto pyobj { std::make_shared<PyObj::VS>(1, 2, 3) };

    // Symbol
    Utils::Log::debug("Testing symbol creation functions...");
    symbol<Ex::Bool>(claricpp_create_symbol_bool(name), name, 0);
    symbol<Ex::String>(claricpp_create_symbol_string(name, bl), name, bl);
    symbol<Ex::VS>(claricpp_create_symbol_vs(name, bl), name, bl);
    symbol<Ex::FP>(claricpp_create_symbol_fp(name, bl), name, bl);
    symbol<Ex::BV>(claricpp_create_symbol_bv(name, bl), name, bl);

    // Literal
    Utils::Log::debug("Testing literal creation functions...");
    literal<Ex::Bool, bool>(claricpp_create_literal_bool(true), true, 0);
    literal<Ex::String, std::string>(claricpp_create_literal_string(name), name,
                                     std::strlen(name) * C_CHAR_BIT);
    literal<Ex::FP, float>(claricpp_create_literal_fp_float(3.f), 3.f, 32); // NOLINT
    literal<Ex::FP, double>(claricpp_create_literal_fp_double(3.), 3., 64); // NOLINT
    literal<Ex::VS, PyObj::VSPtr>(claricpp_create_literal_vs(1, 2, n), pyobj, n);
    literal<Ex::BV, uint8_t>(claricpp_create_literal_bv_u8(n), n, 8);    // NOLINT
    literal<Ex::BV, uint16_t>(claricpp_create_literal_bv_u16(n), n, 16); // NOLINT
    literal<Ex::BV, uint32_t>(claricpp_create_literal_bv_u32(n), n, 32); // NOLINT
    literal<Ex::BV, uint64_t>(claricpp_create_literal_bv_u64(n), n, 64); // NOLINT
    literal<Ex::BV, BigInt>(claricpp_create_literal_bv_big_int_mode_str("10", n),
                            BigInt { "10", n }, n);
    literal<Ex::BV, BigInt>(claricpp_create_literal_bv_big_int_mode_int("10", n), BigInt { 10, n },
                            n);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(create)
