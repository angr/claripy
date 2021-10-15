/** @file */
extern "C" {
#include "api.h"
}
#include "api_private.hpp"

// @todo: Handle exceptions

// Static checks
static_assert(sizeof(std::size_t) == sizeof(Constants::UInt) && std::is_unsigned_v<std::size_t>,
              "Constants::UInt needs to be changed");
static_assert(std::is_same_v<SIZE_T, Constants::UInt>, "SIZE_T needs to be changed");
static_assert(std::is_same_v<VS_T, PyObj::Base::Ref>, "VS_T needs to be changed");
static_assert(std::is_same_v<HASH_T, Hash::Hash>, "HASH_T needs to be changed");

/********************************************************************/
/*                            Annotation                            */
/********************************************************************/

extern "C" {

ClaricppAnnotation *claricpp_annotation_new_base() {
    return API::to_c(Annotation::factory<Annotation::Base>());
}

ClaricppAnnotation *claricpp_annotation_new_simplification_avoicance() {
    return API::to_c(Annotation::factory<Annotation::SimplificationAvoidance>());
}

ClaricppSPAV *claricpp_annotation_create_spav(const ClaricppAnnotation *const *const list,
                                              const SIZE_T len) {
    Annotation::Vec::RawVec raw;
    raw.reserve(len);
    for (SIZE_T i = 0; i < len; ++i) {
        raw.emplace_back(list[i]->ptr);
    }
    using CV = Utils::InternalType<Annotation::SPAV>;
    return API::to_c(std::make_shared<CV>(std::move(raw)));
}
}

/********************************************************************/
/*                              Create                              */
/********************************************************************/

extern "C" {

// Symbol

ClaricppExpr *claricpp_create_symbol_bool(const char *const name) {
    return API::to_c(Create::symbol(std::string { name }));
}

/** A local macro used for consistency */
#define CREATE_SYM(TYPE, NAME)                                                                    \
    ClaricppExpr *claricpp_create_symbol_##NAME(const char *const name,                           \
                                                const SIZE_T bit_length) {                        \
        return API::to_c(Create::symbol<Expression::TYPE>(std::string { name }, bit_length));     \
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
    ClaricppExpr *claricpp_create_literal_##NAME(const TYPE value) {                              \
        return API::to_c(Create::literal(value));                                                 \
    }

CREATE_LIT(bool, bool);
CREATE_LIT(char *const, string);
CREATE_LIT(float, float);
CREATE_LIT(double, double);

ClaricppExpr *claricpp_create_literal_vs(const HASH_T hash, const VS_T value,
                                         const SIZE_T bit_length) {
    return API::to_c(Create::literal(std::make_shared<PyObj::VS>(hash, value, bit_length)));
}

CREATE_LIT(uint8_t, u8);
CREATE_LIT(uint16_t, u16);
CREATE_LIT(uint32_t, u32);
CREATE_LIT(uint64_t, u64);

ClaricppExpr *claricpp_create_literal_bv_big_int_mode_str(PyStr value, const SIZE_T bit_length) {
    return API::to_c(Create::literal(BigInt { value, bit_length }));
}

ClaricppExpr *claricpp_create_literal_bv_big_int_mode_int(PyStr value, const SIZE_T bit_length) {
    return API::to_c(Create::literal(BigInt { BigInt::Int { value }, bit_length }));
}

// Cleanup
#undef CREATE_LIT
}
