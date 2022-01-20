/**
 * @file
 * \ingroup unittest
 */
#include "exc.hpp"
#include "testlib.hpp"


/** Used to try to get valid expr and op pointers */
template <typename E, typename O> static auto get_pointers(const ClaricppExpr in) {
    const Expr::RawPtr exp { API::to_cpp(in).get() };
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
    const char name[] { "name" }; // NOLINT
    const SIZE_T bl { 64_ui };
    const uint8_t n { 8 };
    const auto md { Mode::FP::Rounding::TowardsZero };
    const auto wid { Mode::FP::dbl };

    // Non-trivial constants
    const auto pyobj { std::make_shared<PyObj::VS>(1, 2, 3) };
    const auto bool_sym { Create::symbol("test") };
    const auto bool_true { Create::literal(true) };
    const auto bv_sym { Create::symbol<Expr::BV>("bv", 64) };
    const auto fp_sym { Create::symbol<Expr::FP>("fp", 64) };
    const auto string_sym { Create::symbol<Expr::String>("string", 64) };
    const auto string_sym2 { Create::symbol<Expr::String>("string2", 64) };
    const auto bv_64 { Create::literal(UInt { 64 }) };
    const auto fp_64 { Create::literal(64.) };

    // Symbol
    Util::Log::debug("Testing symbol creation functions...");
    symbol<Expr::Bool>(exc(claricpp_create_symbol_bool(name, { nullptr })), name, 0);
    symbol<Expr::String>(exc(claricpp_create_symbol_string(name, bl, { nullptr })), name, bl);
    symbol<Expr::VS>(exc(claricpp_create_symbol_vs(name, bl, { nullptr })), name, bl);
    symbol<Expr::FP>(exc(claricpp_create_symbol_fp(name, bl, { nullptr })), name, bl);
    symbol<Expr::BV>(exc(claricpp_create_symbol_bv(name, bl, { nullptr })), name, bl);

    // Literal
    Util::Log::debug("Testing literal creation functions...");
    literal<Expr::Bool, bool>(exc(claricpp_create_literal_bool(TRUE, { nullptr })), true, 0);
    literal<Expr::String, std::string>(exc(claricpp_create_literal_string(name, { nullptr })), name,
                                       std::strlen(name) * C_CHAR_BIT);
    literal<Expr::FP, float>(exc(claricpp_create_literal_fp_float(3.F, { nullptr })), 3.F,
                             32); // NOLINT
    literal<Expr::FP, double>(exc(claricpp_create_literal_fp_double(3., { nullptr })), 3.,
                              64); // NOLINT
    literal<Expr::VS, PyObj::VSPtr>(exc(claricpp_create_literal_vs(1, 2, n, { nullptr })), pyobj,
                                    n);                                                   // NOLINT
    literal<Expr::BV, uint8_t>(exc(claricpp_create_literal_bv_u8(n, { nullptr })), n, 8); // NOLINT
    literal<Expr::BV, uint16_t>(exc(claricpp_create_literal_bv_u16(n, { nullptr })), n,
                                16); // NOLINT
    literal<Expr::BV, uint32_t>(exc(claricpp_create_literal_bv_u32(n, { nullptr })), n,
                                32); // NOLINT
    literal<Expr::BV, uint64_t>(exc(claricpp_create_literal_bv_u64(n, { nullptr })), n,
                                64); // NOLINT
    literal<Expr::BV, BigInt>(
        exc(claricpp_create_literal_bv_big_int_mode_str("10", n, { nullptr })), BigInt { "10", n },
        n);
    literal<Expr::BV, BigInt>(
        exc(claricpp_create_literal_bv_big_int_mode_int("10", n, { nullptr })), BigInt { 10, n },
        n);

    // Non-Trivial

    Util::Log::debug("Testing extract...");
    const auto extract { exc(claricpp_create_extract(2, 1, API::copy_to_c(bv_sym), { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(extract)->hash == Create::extract(2, 1, bv_sym)->hash);
    UNITTEST_ASSERT(API::to_cpp(extract)->hash != Create::extract(1, 0, bv_sym)->hash);

    Util::Log::debug("Testing if...");
    const auto if_ { exc(claricpp_create_if(API::copy_to_c(bool_sym), API::copy_to_c(bv_sym),
                                            API::copy_to_c(bv_64), { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(if_)->hash == Create::if_(bool_sym, bv_sym, bv_64)->hash);
    UNITTEST_ASSERT(API::to_cpp(if_)->hash != Create::if_(bool_sym, bv_64, bv_64)->hash);

    // Macros

    /** A local macro used for testing */
#define UNARY(CF, CPPF, TYPE, OTHER)                                                               \
    Util::Log::debug("Testing " #CPPF "...");                                                      \
    const auto test_##CF { exc(claricpp_create_##CF(API::copy_to_c(TYPE##_sym), { nullptr })) };   \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash == Create::CPPF(TYPE##_sym)->hash);               \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash != Create::CPPF(TYPE##_##OTHER)->hash)

    /** A local macro used for testing */
#define UINT_BINARY(CF, CPPF, TYPE)                                                                \
    Util::Log::debug("Testing " #CPPF "...");                                                      \
    const auto test_##CF { exc(                                                                    \
        claricpp_create_##CF(API::copy_to_c(TYPE##_sym), 4, { nullptr })) };                       \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash == Create::CPPF(TYPE##_sym, 4)->hash);            \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash != Create::CPPF(TYPE##_sym, 5)->hash)

/** A local macro used for testing */
#define BINARY(CF, CPPF, ARG, BAD_ARG)                                                             \
    Util::Log::debug("Testing " #CPPF "...");                                                      \
    const auto test_##CF { exc(                                                                    \
        claricpp_create_##CF(API::copy_to_c(ARG), API::copy_to_c(ARG), { nullptr })) };            \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash == Create::CPPF(ARG, ARG)->hash);                 \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash != Create::CPPF(ARG, BAD_ARG)->hash)

/** A local macro used for testing */
#define TERNARY(CF, CPPF, ARG, BAD_ARG)                                                            \
    Util::Log::debug("Testing " #CPPF "...");                                                      \
    const auto test_##CF { exc(claricpp_create_##CF(API::copy_to_c(ARG), API::copy_to_c(ARG),      \
                                                    API::copy_to_c(ARG), { nullptr })) };          \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash == Create::CPPF(ARG, ARG, ARG)->hash);            \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash != Create::CPPF(ARG, ARG, BAD_ARG)->hash);

/** A local macro used for testing */
#define MODE_BINARY(FUN, MODE)                                                                     \
    Util::Log::debug("Testing FP::" #FUN "...");                                                   \
    const auto test_fp_##FUN { exc(claricpp_create_fp_##FUN(                                       \
        API::copy_to_c(fp_sym), API::copy_to_c(fp_sym), API::mode(MODE), { nullptr })) };          \
    UNITTEST_ASSERT(API::to_cpp(test_fp_##FUN)->hash ==                                            \
                    Create::FP::FUN(fp_sym, fp_sym, MODE)->hash);                                  \
    UNITTEST_ASSERT(API::to_cpp(test_fp_##FUN)->hash != Create::FP::FUN(fp_sym, fp_64, MODE)->hash);

/** A local macro used for testing */
#define FLAT(CF, CPPF, INP, REAL_INP, BAD_INP)                                                     \
    Util::Log::debug("Testing " #CPPF "...");                                                      \
    const auto test_##CF { exc(claricpp_create_##CF(INP, (REAL_INP).size(), { nullptr })) };       \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash == Create::CPPF((REAL_INP))->hash);               \
    UNITTEST_ASSERT(API::to_cpp(test_##CF)->hash != Create::CPPF((BAD_INP))->hash)

    // Trivial

    UNARY(abs, abs, fp, 64);
    UNARY(neg, neg, bv, 64);
    UNARY(not, not_, bool, true);
    UNARY(invert, invert, bv, 64);
    UNARY(reverse, reverse, bv, 64);

    UINT_BINARY(sign_ext, sign_ext, bv);
    UINT_BINARY(zero_ext, zero_ext, bv);

    // Comparisons
    BINARY(eq, eq, bv_64, bv_sym);
    BINARY(neq, neq, bv_64, bv_sym);
    using Cmp = Mode::Compare;
    BINARY(slt, compare<Cmp::Signed | Cmp::Less | Cmp::Neq>, bv_64, bv_sym);
    BINARY(sle, compare<Cmp::Signed | Cmp::Less | Cmp::Eq>, bv_64, bv_sym);
    BINARY(sgt, compare<Cmp::Signed | Cmp::Greater | Cmp::Neq>, bv_64, bv_sym);
    BINARY(sge, compare<Cmp::Signed | Cmp::Greater | Cmp::Eq>, bv_64, bv_sym);
    BINARY(ult, compare<Cmp::Unsigned | Cmp::Less | Cmp::Neq>, bv_64, bv_sym);
    BINARY(ule, compare<Cmp::Unsigned | Cmp::Less | Cmp::Eq>, bv_64, bv_sym);
    BINARY(ugt, compare<Cmp::Unsigned | Cmp::Greater | Cmp::Neq>, bv_64, bv_sym);
    BINARY(uge, compare<Cmp::Unsigned | Cmp::Greater | Cmp::Eq>, bv_64, bv_sym);

    // Math
    BINARY(sub, sub, bv_64, bv_sym);
    BINARY(sdiv, div<true>, bv_64, bv_sym);
    BINARY(udiv, div<false>, bv_64, bv_sym);
    BINARY(smod, mod<true>, bv_64, bv_sym);
    BINARY(umod, mod<false>, bv_64, bv_sym);

    // Bitwise
    BINARY(shift_left, shift<Mode::Shift::Left>, bv_64, bv_sym);
    BINARY(shift_logical_right, shift<Mode::Shift::LogicalRight>, bv_64, bv_sym);
    BINARY(shift_arithmetic_right, shift<Mode::Shift::ArithmeticRight>, bv_64, bv_sym);

    // Misc
    BINARY(widen, widen, bv_64, bv_sym);
    BINARY(union, union_, bv_64, bv_sym);
    BINARY(intersection, intersection_, bv_64, bv_sym);
    BINARY(concat, concat, bv_64, bv_sym);

    // Math
    const ClaricppExpr flat_bv_entry { API::to_c(Expr::BasePtr { bv_64 }) };
    const ClaricppExpr flat_bv[] { flat_bv_entry, flat_bv_entry, flat_bv_entry }; // NOLINT
    const auto real_flat_bv { [&bv_64]() { return Op::FlatArgs { bv_64, bv_64, bv_64 }; } };
    const auto bad_flat_bv { [&bv_64, &bv_sym]() {
        return Op::FlatArgs { bv_64, bv_64, bv_sym };
    } };
    FLAT(add, add, flat_bv, real_flat_bv(), bad_flat_bv());
    FLAT(mul, mul, flat_bv, real_flat_bv(), bad_flat_bv());

    // Logical
    FLAT(or, or_, flat_bv, real_flat_bv(), bad_flat_bv());
    FLAT(and, and_, flat_bv, real_flat_bv(), bad_flat_bv());
    FLAT(xor, xor_, flat_bv, real_flat_bv(), bad_flat_bv());

    // String

    // Non-Trivial
    Util::Log::debug("Testing String::from_int...");
    const auto sfi { exc(claricpp_create_string_from_int(API::copy_to_c(bv_64), { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(sfi)->hash == Create::String::from_int(bv_64)->hash);
    UNITTEST_ASSERT(API::to_cpp(sfi)->hash != Create::String::from_int(bv_sym)->hash);

    Util::Log::debug("Testing String::index_of...");
    const auto sif { exc(
        claricpp_create_string_index_of(API::copy_to_c(string_sym), API::copy_to_c(string_sym),
                                        API::copy_to_c(bv_sym), bl, { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(sif)->hash ==
                    Create::String::index_of(string_sym, string_sym, bv_sym, bl)->hash);
    UNITTEST_ASSERT(API::to_cpp(sif)->hash !=
                    Create::String::index_of(string_sym, string_sym2, bv_sym, bl)->hash);

    Util::Log::debug("Testing String::replace...");
    const auto sr { exc(claricpp_create_string_replace(API::copy_to_c(string_sym),
                                                       API::copy_to_c(string_sym),
                                                       API::copy_to_c(string_sym), { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(sr)->hash ==
                    Create::String::replace(string_sym, string_sym, string_sym)->hash);
    UNITTEST_ASSERT(API::to_cpp(sr)->hash !=
                    Create::String::replace(string_sym, string_sym, string_sym2)->hash);

    Util::Log::debug("Testing String::sub_string...");
    const auto ss { exc(claricpp_create_string_sub_string(
        API::copy_to_c(bv_sym), API::copy_to_c(bv_sym), API::copy_to_c(string_sym), { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(ss)->hash ==
                    Create::String::sub_string(bv_sym, bv_sym, string_sym)->hash);
    UNITTEST_ASSERT(API::to_cpp(ss)->hash !=
                    Create::String::sub_string(bv_sym, bv_sym, string_sym2)->hash);

    // Trivial
    UNARY(string_is_digit, String::is_digit, string, sym2);

    UINT_BINARY(string_to_int, String::to_int, string);
    UINT_BINARY(string_len, String::len, string);

    BINARY(string_contains, String::contains, string_sym, string_sym2);
    BINARY(string_prefix_of, String::prefix_of, string_sym, string_sym2);
    BINARY(string_suffix_of, String::suffix_of, string_sym, string_sym2);

    // FP

    // Non-Trivial
    Util::Log::debug("Testing FP::from_2s_complement_bv<true>...");
    (void) Create::FP::from_2s_complement_bv<true>(md, bv_sym, wid);
    const auto fp2bvs { exc(claricpp_create_fp_from_2s_complement_bv_signed(
        API::mode(md), API::copy_to_c(bv_sym), wid.exp, wid.mantissa, { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(fp2bvs)->hash ==
                    Create::FP::from_2s_complement_bv<true>(md, bv_sym, wid)->hash);
    UNITTEST_ASSERT(API::to_cpp(fp2bvs)->hash !=
                    Create::FP::from_2s_complement_bv<true>(md, bv_64, wid)->hash);

    Util::Log::debug("Testing FP::from_2s_complement_bv<false>...");
    (void) Create::FP::from_2s_complement_bv<false>(md, bv_sym, wid);
    const auto fpf2bvs { exc(claricpp_create_fp_from_2s_complement_bv_unsigned(
        API::mode(md), API::copy_to_c(bv_sym), wid.exp, wid.mantissa, { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(fpf2bvs)->hash ==
                    Create::FP::from_2s_complement_bv<false>(md, bv_sym, wid)->hash);
    UNITTEST_ASSERT(API::to_cpp(fpf2bvs)->hash !=
                    Create::FP::from_2s_complement_bv<false>(md, bv_64, wid)->hash);

    Util::Log::debug("Testing FP::from_fp...");
    const auto fpffp { exc(claricpp_create_fp_from_fp(API::mode(md), API::copy_to_c(fp_sym),
                                                      wid.exp, wid.mantissa, { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(fpffp)->hash == Create::FP::from_fp(md, fp_sym, wid)->hash);
    UNITTEST_ASSERT(API::to_cpp(fpffp)->hash != Create::FP::from_fp(md, fp_64, wid)->hash);

    Util::Log::debug("Testing FP::from_not_2s_complement_bv...");
    const auto fpfn2bv { exc(claricpp_create_fp_from_not_2s_complement_bv(
        API::copy_to_c(bv_sym), wid.exp, wid.mantissa, { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(fpfn2bv)->hash ==
                    Create::FP::from_not_2s_complement_bv(bv_sym, wid)->hash);
    UNITTEST_ASSERT(API::to_cpp(fpfn2bv)->hash !=
                    Create::FP::from_not_2s_complement_bv(bv_64, wid)->hash);

    Util::Log::debug("Testing FP::to_bv<true>...");
    const auto fpt2bvs { exc(
        claricpp_create_fp_to_bv_signed(API::mode(md), API::copy_to_c(fp_sym), bl, { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(fpt2bvs)->hash == Create::FP::to_bv<true>(md, fp_sym, bl)->hash);
    UNITTEST_ASSERT(API::to_cpp(fpt2bvs)->hash != Create::FP::to_bv<true>(md, fp_64, bl)->hash);

    Util::Log::debug("Testing FP::to_bv<false>...");
    const auto fpt2bvu { exc(claricpp_create_fp_to_bv_unsigned(
        API::mode(md), API::copy_to_c(fp_sym), bl, { nullptr })) };
    UNITTEST_ASSERT(API::to_cpp(fpt2bvu)->hash == Create::FP::to_bv<false>(md, fp_sym, bl)->hash);
    UNITTEST_ASSERT(API::to_cpp(fpt2bvu)->hash != Create::FP::to_bv<false>(md, fp_64, bl)->hash);

    // Trivial
    UNARY(fp_to_ieee_bv, FP::to_ieee_bv, fp, 64);

    MODE_BINARY(add, md);
    MODE_BINARY(sub, md);
    MODE_BINARY(mul, md);
    MODE_BINARY(div, md);

    TERNARY(fp_fp, FP::fp, bv_sym, bv_64);
}

// Define the test
UNITTEST_DEFINE_MAIN_TEST(create)
