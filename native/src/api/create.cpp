/** @file */
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

// Symbol

ClaricppExpr claricpp_create_symbol_bool(PyStr name, ClaricppSPAV spav) {
    static constexpr Expr::BasePtr (*const f)(std::string &&,
                                              Annotation::SPAV &&) { Create::symbol };
    return make(f, spav, std::string { name });
}

/** A local macro used for consistency */
#define CREATE_SYM(TYPE, NAME)                                                                    \
    ClaricppExpr claricpp_create_symbol_##NAME(PyStr name, const SIZE_T bit_length,               \
                                               ClaricppSPAV spav) {                               \
        return make(Create::symbol<Expr::TYPE>, spav, std::string { name }, bit_length);          \
    }

CREATE_SYM(String, string);
CREATE_SYM(VS, vs);
CREATE_SYM(FP, fp);
CREATE_SYM(BV, bv);

// Cleanup
#undef CREATE_SYM

// Literal

/** A local macro used for consistency */
#define CREATE_LIT(TYPE, NAME)                                                                    \
    ClaricppExpr claricpp_create_literal_##NAME(const TYPE value, ClaricppSPAV spav) {            \
        static constexpr Expr::BasePtr (*const f)(TYPE, Annotation::SPAV &&) { Create::literal }; \
        return make(f, spav, value);                                                              \
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
    static constexpr Expr::BasePtr (*const f)(BigInt &&, Annotation::SPAV &&) { Create::literal };
    return make(f, spav, BigInt { BigInt::Str { value }, bit_length });
}

ClaricppExpr claricpp_create_literal_bv_big_int_mode_int(PyStr value, const SIZE_T bit_length,
                                                         ClaricppSPAV spav) {
    static constexpr Expr::BasePtr (*const f)(BigInt &&, Annotation::SPAV &&) { Create::literal };
    return make(f, spav, BigInt { BigInt::Int { value }, bit_length });
}

// Non Trivial

ClaricppExpr claricpp_create_extract(const SIZE_T high, const SIZE_T low, const ClaricppExpr from,
                                     ClaricppSPAV spav) {
    return make(Create::extract, spav, high, low, API::to_cpp_ref(from));
}

ClaricppExpr claricpp_create_if(const ClaricppExpr cond, const ClaricppExpr left,
                                const ClaricppExpr right, ClaricppSPAV spav) {
    return make(Create::if_, spav, API::to_cpp_ref(cond), API::to_cpp_ref(left),
                API::to_cpp_ref(right));
}

// Trivial unary

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
}
