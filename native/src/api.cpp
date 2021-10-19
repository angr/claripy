/** @file */
#include "api_private.hpp"

// @todo: Handle exceptions


// Static checks
/** A local macro used for static tests */
#define SAME_U(A, B) (sizeof(A) == sizeof(B) && std::is_unsigned_v<A> && std::is_unsigned_v<B>)
static_assert(SAME_U(std::size_t, Constants::UInt), "Constants::UInt needs to be changed");
static_assert(SAME_U(SIZE_T, Constants::UInt), "Constants::UInt needs to be changed");
static_assert(SAME_U(VS_T, PyObj::Base::Ref), "VS_T needs to be changed");
static_assert(SAME_U(HASH_T, Hash::Hash), "HASH_T needs to be changed");
static_assert(std::is_same_v<Constants::CCSC, PyStr>, "PyStr needs to be changed");
static_assert(std::is_same_v<PyStr, ARRAY_IN(char)>, "ARRAY_IN needs to be changed");
// Cleanup
#undef SAME_U

/********************************************************************/
/*                            Annotation                            */
/********************************************************************/

extern "C" {

ClaricppAnnotation claricpp_annotation_new_base() {
    return API::to_c(Annotation::factory<Annotation::Base>());
}

ClaricppAnnotation claricpp_annotation_new_simplification_avoicance() {
    return API::to_c(Annotation::factory<Annotation::SimplificationAvoidance>());
}

ClaricppSPAV claricpp_annotation_create_spav(ARRAY_IN(ClaricppAnnotation) list, const SIZE_T len) {
    Annotation::Vec::RawVec raw;
    raw.reserve(len);
    for (SIZE_T i = 0; i < len; ++i) {
        raw.emplace_back(API::to_cpp_ref(list[i])); // NOLINT
    }
    using CV = Utils::InternalType<Annotation::SPAV>;
    return API::to_c(std::make_shared<CV>(std::move(raw)));
}
}

/********************************************************************/
/*                              Create                              */
/********************************************************************/


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
    static constexpr Expression::BasePtr (*const f)(std::string &&,
                                                    Annotation::SPAV &&) { Create::symbol };
    return make(f, spav, std::string { name });
}

/** A local macro used for consistency */
#define CREATE_SYM(TYPE, NAME)                                                                    \
    ClaricppExpr claricpp_create_symbol_##NAME(PyStr name, const SIZE_T bit_length,               \
                                               ClaricppSPAV spav) {                               \
        return make(Create::symbol<Expression::TYPE>, spav, std::string { name }, bit_length);    \
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
        static constexpr Expression::BasePtr (*const f)(TYPE,                                     \
                                                        Annotation::SPAV &&) { Create::literal }; \
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
    static constexpr Expression::BasePtr (*const f)(std::string &&,
                                                    Annotation::SPAV &&) { Create::literal };
    return make(f, spav, std::string { str });
}

ClaricppExpr claricpp_create_literal_vs(const HASH_T hash, const VS_T value,
                                        const SIZE_T bit_length, ClaricppSPAV spav) {
    static constexpr Expression::BasePtr (*const f)(PyObj::VSPtr &&,
                                                    Annotation::SPAV &&) { Create::literal };
    return make(f, spav, std::make_shared<PyObj::VS>(hash, value, bit_length));
}

ClaricppExpr claricpp_create_literal_bv_big_int_mode_str(PyStr value, const SIZE_T bit_length,
                                                         ClaricppSPAV spav) {
    static constexpr Expression::BasePtr (*const f)(BigInt &&,
                                                    Annotation::SPAV &&) { Create::literal };
    return make(f, spav, BigInt { BigInt::Str { value }, bit_length });
}

ClaricppExpr claricpp_create_literal_bv_big_int_mode_int(PyStr value, const SIZE_T bit_length,
                                                         ClaricppSPAV spav) {
    static constexpr Expression::BasePtr (*const f)(BigInt &&,
                                                    Annotation::SPAV &&) { Create::literal };
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
}
