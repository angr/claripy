/**
 * @file
 * \ingroup api
 */
#include "../create.hpp"

#include "cpp.hpp"


/** A local helper function for create methods */
template <typename F, typename... Args>
static inline auto make(const F &f, ClaricppSPAV &spav, Args &&...args) {
    if (spav.ptr == nullptr) {
        return API::to_c(f(std::forward<Args>(args)..., { nullptr }));
    }
    auto ret { API::to_c(f(std::forward<Args>(args)..., std::move(API::to_cpp_ref(spav)))) };
    API::free(spav);
    return ret;
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

/** A local macro used for consistency */
#define CREATE_LIT(TYPE, NAME)                                                                     \
    ClaricppExpr claricpp_create_literal_##NAME(const TYPE value, ClaricppSPAV spav) {             \
        static constexpr Expr::BasePtr (*const f)(TYPE, Annotation::SPAV &&) { Create::literal };  \
        return make(f, spav, value);                                                               \
    }

    CREATE_LIT(bool, bool);
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
        return make(Create::extract, spav, high, low, API::to_cpp_ref(from));
    }

    ClaricppExpr claricpp_create_if(const ClaricppExpr cond, const ClaricppExpr left,
                                    const ClaricppExpr right, ClaricppSPAV spav) {
        return make(Create::if_, spav, API::to_cpp_ref(cond), API::to_cpp_ref(left),
                    API::to_cpp_ref(right));
    }

    /********************************************************************/
    /*                          Trivial Unary                           */
    /********************************************************************/

    ClaricppExpr claricpp_create_abs(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::abs, spav, API::to_cpp_ref(x));
    }

    ClaricppExpr claricpp_create_neg(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::neg, spav, API::to_cpp_ref(x));
    }

    ClaricppExpr claricpp_create_not(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::not_, spav, API::to_cpp_ref(x));
    }

    ClaricppExpr claricpp_create_invert(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::invert, spav, API::to_cpp_ref(x));
    }

    ClaricppExpr claricpp_create_reverse(const ClaricppExpr x, ClaricppSPAV spav) {
        return make(Create::reverse, spav, API::to_cpp_ref(x));
    }

    /********************************************************************/
    /*                        Trivial UInt Binary                       */
    /********************************************************************/

    ClaricppExpr claricpp_create_sign_ext(const ClaricppExpr expr, const UINT integer,
                                          ClaricppSPAV spav) {
        return make(Create::sign_ext, spav, API::to_cpp_ref(expr), integer);
    }

    ClaricppExpr claricpp_create_zero_ext(const ClaricppExpr expr, const UINT integer,
                                          ClaricppSPAV spav) {
        return make(Create::zero_ext, spav, API::to_cpp_ref(expr), integer);
    }

    /********************************************************************/
    /*                          Trivial Binary                          */
    /********************************************************************/

    // Comparisons

    ClaricppExpr claricpp_create_eq(const ClaricppExpr left, const ClaricppExpr right,
                                    ClaricppSPAV spav) {
        return make(Create::eq, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_neq(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        return make(Create::neq, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_slt(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        using C = Mode::Compare;
        static constexpr auto mask { C::Signed | C::Less | C::Neq };
        return make(Create::compare<mask>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_sle(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        using C = Mode::Compare;
        static constexpr auto mask { C::Signed | C::Less | C::Eq };
        return make(Create::compare<mask>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_sgt(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        using C = Mode::Compare;
        static constexpr auto mask { C::Signed | C::Greater | C::Neq };
        return make(Create::compare<mask>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_sge(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        using C = Mode::Compare;
        static constexpr auto mask { C::Signed | C::Greater | C::Eq };
        return make(Create::compare<mask>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_ult(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        using C = Mode::Compare;
        static constexpr auto mask { C::Unsigned | C::Less | C::Neq };
        return make(Create::compare<mask>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_ule(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        using C = Mode::Compare;
        static constexpr auto mask { C::Unsigned | C::Less | C::Eq };
        return make(Create::compare<mask>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_ugt(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        using C = Mode::Compare;
        static constexpr auto mask { C::Unsigned | C::Greater | C::Neq };
        return make(Create::compare<mask>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_uge(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        using C = Mode::Compare;
        static constexpr auto mask { C::Unsigned | C::Greater | C::Eq };
        return make(Create::compare<mask>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    // Math

    ClaricppExpr claricpp_create_sub(const ClaricppExpr left, const ClaricppExpr right,
                                     ClaricppSPAV spav) {
        return make(Create::sub, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_sdiv(const ClaricppExpr left, const ClaricppExpr right,
                                      ClaricppSPAV spav) {
        return make(Create::div<true>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_udiv(const ClaricppExpr left, const ClaricppExpr right,
                                      ClaricppSPAV spav) {
        return make(Create::div<false>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_smod(const ClaricppExpr left, const ClaricppExpr right,
                                      ClaricppSPAV spav) {
        return make(Create::mod<true>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_umod(const ClaricppExpr left, const ClaricppExpr right,
                                      ClaricppSPAV spav) {
        return make(Create::mod<false>, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    // Bitwise

    ClaricppExpr claricpp_create_shift_left(const ClaricppExpr left, const ClaricppExpr right,
                                            ClaricppSPAV spav) {
        return make(Create::shift<Mode::Shift::Left>, spav, API::to_cpp_ref(left),
                    API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_shift_logical_right(const ClaricppExpr left,
                                                     const ClaricppExpr right, ClaricppSPAV spav) {
        return make(Create::shift<Mode::Shift::LogicalRight>, spav, API::to_cpp_ref(left),
                    API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_shift_arithmetic_right(const ClaricppExpr left,
                                                        const ClaricppExpr right,
                                                        ClaricppSPAV spav) {
        return make(Create::shift<Mode::Shift::ArithmeticRight>, spav, API::to_cpp_ref(left),
                    API::to_cpp_ref(right));
    }

    // Misc

    ClaricppExpr claricpp_create_widen(const ClaricppExpr left, const ClaricppExpr right,
                                       ClaricppSPAV spav) {
        return make(Create::widen, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_union(const ClaricppExpr left, const ClaricppExpr right,
                                       ClaricppSPAV spav) {
        return make(Create::union_, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_intersection(const ClaricppExpr left, const ClaricppExpr right,
                                              ClaricppSPAV spav) {
        return make(Create::intersection_, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
    }

    ClaricppExpr claricpp_create_concat(const ClaricppExpr left, const ClaricppExpr right,
                                        ClaricppSPAV spav) {
        return make(Create::concat, spav, API::to_cpp_ref(left), API::to_cpp_ref(right));
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
}
