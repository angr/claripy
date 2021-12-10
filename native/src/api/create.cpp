/**
 * @file
 * \ingroup api
 */
#include "../create.hpp"

#include "cpp.hpp"


/** A local helper function for create methods */
template <typename F, typename... Args>
static inline auto make(const F &f, ClaricppSPAV &spav, Args &&...args) {
    using CppType = std::invoke_result_t<F, Args..., Annotation::SPAV>;
    using Ret = decltype(API::to_c(std::declval<CppType>()));
    API_FUNC_START
    if (spav.ptr == nullptr) {
        return API::to_c(f(std::forward<Args>(args)..., { nullptr }));
    }
    Ret ret { API::to_c(f(std::forward<Args>(args)..., std::move(API::to_cpp(spav)))) };
    API::free(spav);
    return ret;
    API_FUNC_END_NO_RETURN
    return Ret { 0 }; // Required since we used the no return statement
}

extern "C" {

    /********************************************************************/
    /*                              Symbol                              */
    /********************************************************************/

    ClaricppExpr claricpp_create_symbol_bool(PyStr name, ClaricppSPAV spav) {
        static constexpr Expr::BasePtr (*const f)(std::string &&,
                                                  Annotation::SPAV &&) { Create::symbol };
        return make(f, spav, std::string { name });
    }

/** A local macro used for consistency */
#define CREATE_SYM(TYPE, NAME)                                                                     \
    ClaricppExpr claricpp_create_symbol_##NAME(PyStr name, const SIZE_T bit_length,                \
                                               ClaricppSPAV spav) {                                \
        return make(Create::symbol<Expr::TYPE>, spav, std::string { name }, bit_length);           \
    }

    CREATE_SYM(String, string);
    CREATE_SYM(VS, vs);
    CREATE_SYM(FP, fp);
    CREATE_SYM(BV, bv);

// Cleanup
#undef CREATE_SYM

    /********************************************************************/
    /*                             Literal                              */
    /********************************************************************/

    ClaricppExpr claricpp_create_literal_bool(const BOOL value, ClaricppSPAV spav) {
        static constexpr Expr::BasePtr (*const f)(bool, Annotation::SPAV &&) { Create::literal };
        return make(f, spav, static_cast<bool>(value));
    }

/** A local macro used for consistency */
#define CREATE_LIT(TYPE, NAME)                                                                     \
    ClaricppExpr claricpp_create_literal_##NAME(const TYPE value, ClaricppSPAV spav) {             \
        static constexpr Expr::BasePtr (*const f)(TYPE, Annotation::SPAV &&) { Create::literal };  \
        return make(f, spav, value);                                                               \
    }

    CREATE_LIT(float, fp_float);
    CREATE_LIT(double, fp_double);
    CREATE_LIT(uint8_t, bv_u8);
    CREATE_LIT(uint16_t, bv_u16);
    CREATE_LIT(uint32_t, bv_u32);
    CREATE_LIT(uint64_t, bv_u64);

// Cleanup
#undef CREATE_LIT

    ClaricppExpr claricpp_create_literal_string(PyStr str, ClaricppSPAV spav) {
        static constexpr Expr::BasePtr (*const f)(std::string &&,
                                                  Annotation::SPAV &&) { Create::literal };
        return make(f, spav, std::string { str });
    }

    ClaricppExpr claricpp_create_literal_vs(const HASH_T hash, const VS_T value,
                                            const SIZE_T bit_length, ClaricppSPAV spav) {
        static constexpr Expr::BasePtr (*const f)(PyObj::VSPtr &&,
                                                  Annotation::SPAV &&) { Create::literal };
        return make(f, spav, std::make_shared<PyObj::VS>(hash, value, bit_length));
    }

    ClaricppExpr claricpp_create_literal_bv_big_int_mode_str(PyStr value, const SIZE_T bit_length,
                                                             ClaricppSPAV spav) {
        static constexpr Expr::BasePtr (*const f)(BigInt &&,
                                                  Annotation::SPAV &&) { Create::literal };
        return make(f, spav, BigInt { BigInt::Str { value }, bit_length });
    }

    ClaricppExpr claricpp_create_literal_bv_big_int_mode_int(PyStr value, const SIZE_T bit_length,
                                                             ClaricppSPAV spav) {
        static constexpr Expr::BasePtr (*const f)(BigInt &&,
                                                  Annotation::SPAV &&) { Create::literal };
        return make(f, spav, BigInt { BigInt::Int { value }, bit_length });
    }

    /********************************************************************/
    /*                           Non-Trivial                            */
    /********************************************************************/

    ClaricppExpr claricpp_create_extract(const SIZE_T high, const SIZE_T low,
                                         const ClaricppExpr from, ClaricppSPAV spav) {
        return make(Create::extract, spav, high, low, API::to_cpp(from));
    }

    ClaricppExpr claricpp_create_if(const ClaricppExpr cond, const ClaricppExpr if_true,
                                    const ClaricppExpr if_false, ClaricppSPAV spav) {
        return make(Create::if_, spav, API::to_cpp(cond), API::to_cpp(if_true),
                    API::to_cpp(if_false));
    }

    /********************************************************************/
    /*                          Trivial Unary                           */
    /********************************************************************/

    ClaricppExpr claricpp_create_abs(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::abs, spav, API::to_cpp(x));
    }

    ClaricppExpr claricpp_create_neg(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::neg, spav, API::to_cpp(x));
    }

    ClaricppExpr claricpp_create_not(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::not_, spav, API::to_cpp(x));
    }

    ClaricppExpr claricpp_create_invert(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::invert, spav, API::to_cpp(x));
    }

    ClaricppExpr claricpp_create_reverse(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::reverse, spav, API::to_cpp(x));
    }

    /********************************************************************/
    /*                        Trivial UInt Binary                       */
    /********************************************************************/

    ClaricppExpr claricpp_create_sign_ext(const ClaricppExpr expr, const UINT add,
                                          ClaricppSPAV spav) {
        return make(Create::sign_ext, spav, API::to_cpp(expr), add);
    }

    ClaricppExpr claricpp_create_zero_ext(const ClaricppExpr expr, const UINT add,
                                          ClaricppSPAV spav) {
        return make(Create::zero_ext, spav, API::to_cpp(expr), add);
    }

    /********************************************************************/
    /*                          Trivial Binary                          */
    /********************************************************************/

    // Comparisons

    ClaricppExpr claricpp_create_eq(const ClaricppExpr left, const ClaricppExpr right,
                                    ClaricppSPAV spav) {
        return make(Create::eq, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_neq(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        return make(Create::neq, spav, API::to_cpp(left), API::to_cpp(right));
    }

/** A local macro used for consistency */
#define CMP(NAME, FLAGS)                                                                           \
    ClaricppExpr claricpp_create_##NAME(const ClaricppExpr left, const ClaricppExpr right,         \
                                        ClaricppSPAV spav) {                                       \
        using C = Mode::Compare;                                                                   \
        return make(Create::compare<FLAGS>, spav, API::to_cpp(left), API::to_cpp(right));          \
    }

    CMP(slt, C::Signed | C::Less | C::Neq)
    CMP(sle, C::Signed | C::Less | C::Eq)
    CMP(sgt, C::Signed | C::Greater | C::Neq)
    CMP(sge, C::Signed | C::Greater | C::Eq)
    CMP(ult, C::Unsigned | C::Less | C::Neq)
    CMP(ule, C::Unsigned | C::Less | C::Eq)
    CMP(ugt, C::Unsigned | C::Greater | C::Neq)
    CMP(uge, C::Unsigned | C::Greater | C::Eq)

// Cleanup
#undef CMP

    // Math

    ClaricppExpr claricpp_create_sub(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        return make(Create::sub, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_sdiv(const ClaricppExpr left, const ClaricppExpr right,
                                      ClaricppSPAV spav) {
        return make(Create::div<true>, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_udiv(const ClaricppExpr left, const ClaricppExpr right,
                                      ClaricppSPAV spav) {
        return make(Create::div<false>, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_smod(const ClaricppExpr left, const ClaricppExpr right,
                                      ClaricppSPAV spav) {
        return make(Create::mod<true>, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_umod(const ClaricppExpr left, const ClaricppExpr right,
                                      ClaricppSPAV spav) {
        return make(Create::mod<false>, spav, API::to_cpp(left), API::to_cpp(right));
    }

    // Bitwise

    ClaricppExpr claricpp_create_shift_left(const ClaricppExpr left, const ClaricppExpr right,
                                            ClaricppSPAV spav) {
        return make(Create::shift<Mode::Shift::Left>, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_shift_logical_right(const ClaricppExpr left,
                                                     const ClaricppExpr right, ClaricppSPAV spav) {
        return make(Create::shift<Mode::Shift::LogicalRight>, spav, API::to_cpp(left),
                    API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_shift_arithmetic_right(const ClaricppExpr left,
                                                        const ClaricppExpr right,
                                                        ClaricppSPAV spav) {
        return make(Create::shift<Mode::Shift::ArithmeticRight>, spav, API::to_cpp(left),
                    API::to_cpp(right));
    }

    // Misc

    ClaricppExpr claricpp_create_widen(const ClaricppExpr left, const ClaricppExpr right,
                                       ClaricppSPAV spav) {
        return make(Create::widen, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_union(const ClaricppExpr left, const ClaricppExpr right,
                                       ClaricppSPAV spav) {
        return make(Create::union_, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_intersection(const ClaricppExpr left, const ClaricppExpr right,
                                              ClaricppSPAV spav) {
        return make(Create::intersection_, spav, API::to_cpp(left), API::to_cpp(right));
    }

    ClaricppExpr claricpp_create_concat(const ClaricppExpr left, const ClaricppExpr right,
                                        ClaricppSPAV spav) {
        return make(Create::concat, spav, API::to_cpp(left), API::to_cpp(right));
    }

    /********************************************************************/
    /*                               Flat                               */
    /********************************************************************/

    // Math

    ClaricppExpr claricpp_create_add(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                     ClaricppSPAV spav) {
        return make(Create::add, spav, API::to_op_args(operands, len));
    }

    ClaricppExpr claricpp_create_mul(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                     ClaricppSPAV spav) {
        return make(Create::mul, spav, API::to_op_args(operands, len));
    }

    // Logical

    ClaricppExpr claricpp_create_or(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                    ClaricppSPAV spav) {
        return make(Create::or_, spav, API::to_op_args(operands, len));
    }

    ClaricppExpr claricpp_create_and(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                     ClaricppSPAV spav) {
        return make(Create::and_, spav, API::to_op_args(operands, len));
    }

    ClaricppExpr claricpp_create_xor(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                     ClaricppSPAV spav) {
        return make(Create::xor_, spav, API::to_op_args(operands, len));
    }

    /********************************************************************/
    /*                              String                              */
    /********************************************************************/

    ClaricppExpr claricpp_create_string_is_digit(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::String::is_digit, spav, API::to_cpp(x));
    }

    ClaricppExpr claricpp_create_string_to_int(const ClaricppExpr expr, const UINT len,
                                               ClaricppSPAV spav) {
        return make(Create::String::to_int, spav, API::to_cpp(expr), len);
    }

    ClaricppExpr claricpp_create_string_len(const ClaricppExpr expr, const UINT len,
                                            ClaricppSPAV spav) {
        return make(Create::String::len, spav, API::to_cpp(expr), len);
    }

    ClaricppExpr claricpp_create_string_contains(const ClaricppExpr full, const ClaricppExpr sub,
                                                 ClaricppSPAV spav) {
        return make(Create::String::contains, spav, API::to_cpp(full), API::to_cpp(sub));
    }

    ClaricppExpr claricpp_create_string_prefix_of(const ClaricppExpr full,
                                                  const ClaricppExpr prefix, ClaricppSPAV spav) {
        return make(Create::String::prefix_of, spav, API::to_cpp(full), API::to_cpp(prefix));
    }

    ClaricppExpr claricpp_create_string_suffix_of(const ClaricppExpr full,
                                                  const ClaricppExpr suffix, ClaricppSPAV spav) {
        return make(Create::String::suffix_of, spav, API::to_cpp(full), API::to_cpp(suffix));
    }

    /********************************************************************/
    /*                                FP                                */
    /********************************************************************/

    ClaricppExpr claricpp_create_fp_to_ieee_bv(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::FP::to_ieee_bv, spav, API::to_cpp(x));
    }

    ClaricppExpr claricpp_create_fp_add(const ClaricppExpr left, const ClaricppExpr right,
                                        const ClaricppRM mode, ClaricppSPAV spav) {
        return make(Create::FP::add, spav, API::to_cpp(left), API::to_cpp(right), API::mode(mode));
    }

    ClaricppExpr claricpp_create_fp_sub(const ClaricppExpr left, const ClaricppExpr right,
                                        const ClaricppRM mode, ClaricppSPAV spav) {
        return make(Create::FP::sub, spav, API::to_cpp(left), API::to_cpp(right), API::mode(mode));
    }

    ClaricppExpr claricpp_create_fp_mul(const ClaricppExpr left, const ClaricppExpr right,
                                        const ClaricppRM mode, ClaricppSPAV spav) {
        return make(Create::FP::mul, spav, API::to_cpp(left), API::to_cpp(right), API::mode(mode));
    }

    ClaricppExpr claricpp_create_fp_div(const ClaricppExpr left, const ClaricppExpr right,
                                        const ClaricppRM mode, ClaricppSPAV spav) {
        return make(Create::FP::div, spav, API::to_cpp(left), API::to_cpp(right), API::mode(mode));
    }
}
