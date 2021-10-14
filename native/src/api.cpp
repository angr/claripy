/** @file */
extern "C" {
#include "api.h"
}

// @todo: Handle exceptions

#include "annotation.hpp"
#include "backend.hpp"
#include "create.hpp"
#include "py_obj.hpp"
#include "simplification.hpp"
#include "utils.hpp"


/********************************************************************/
/*                        Type Declarations                         */
/********************************************************************/

static_assert(sizeof(std::size_t) == sizeof(Constants::UInt) && std::is_unsigned_v<std::size_t>,
              "Constants::UInt needs to be changed");
static_assert(std::is_same_v<SIZE_T, Constants::UInt>, "SIZE_T needs to be changed");
static_assert(std::is_same_v<VS_T, PyObj::Base::Ref>, "VS_T needs to be changed");
static_assert(std::is_same_v<HASH_T, Hash::Hash>, "HASH_T needs to be changed");

extern "C" {

// These types should be structs which contain only a single shared pointer named ptr

struct ClaricppAnnotation final {
    Annotation::BasePtr ptr;
};

struct ClaricppSPAV final {
    Annotation::SPAV ptr;
};

struct ClaricppExpr final {
    Expression::BasePtr ptr;
};
}

/********************************************************************/
/*                             Private                              */
/********************************************************************/

namespace Private {

    /** Maps a C++ type to its C analog */
    template <typename T> struct InternalMap;
    /** A local macro used to add a Map entry */
#define MAP_ADD(CTYPE)                                                                            \
    static_assert(std::is_standard_layout_v<CTYPE>, "Struct must be trivial");                    \
    template <> struct InternalMap<decltype(std::declval<CTYPE>().ptr)> final {                   \
        using Result = CTYPE;                                                                     \
    };                                                                                            \
    static_assert(Utils::is_shared_ptr<decltype(std::declval<CTYPE>().ptr)>,                      \
                  "C++ type must be a shared pointer.");                                          \
    static_assert(sizeof(CTYPE) == sizeof(decltype(std::declval<CTYPE>().ptr)),                   \
                  "Struct should only contain a shared pointer.");

    // Populate InternalMap
    MAP_ADD(ClaricppAnnotation)
    MAP_ADD(ClaricppSPAV)
    MAP_ADD(ClaricppExpr)

// Cleanup
#undef MAP_ADD

    /** A shortcut used to access InternalMap */
    template <typename T> using Map = typename InternalMap<T>::Result;

    static_assert(std::is_same_v<Map<Annotation::BasePtr>, ClaricppAnnotation>, "f");
    /** Heap cache function */
    template <typename In> static inline Map<In> *to_c(In &&x) {
        static thread_local Utils::CHeapCache<In, Map<In>> cache {};
        return cache.move_to_heap(std::forward<In>(x));
    }
    /** Heap cache function with emplacement */
    template <typename In, typename... Args> static inline Map<In> *emplace_to_c(Args &&...args) {
        static thread_local Utils::CHeapCache<In, Map<In>> cache {};
        return cache.emplace_on_heap(std::forward<Args>(args)...);
    }
} // namespace Private

/********************************************************************/
/*                            Annotation                            */
/********************************************************************/

extern "C" {

ClaricppAnnotation *claricpp_annotation_new_base() {
    return Private::to_c(Annotation::factory<Annotation::Base>());
}

ClaricppAnnotation *claricpp_annotation_new_simplification_avoicance() {
    return Private::to_c(Annotation::factory<Annotation::SimplificationAvoidance>());
}

ClaricppSPAV *claricpp_annotation_create_spav(const ClaricppAnnotation *const *const list,
                                              const SIZE_T len) {
    Annotation::Vec::RawVec raw;
    raw.reserve(len);
    for (SIZE_T i = 0; i < len; ++i) {
        raw.emplace_back(list[i]->ptr);
    }
    using CV = Utils::InternalType<Annotation::SPAV>;
    return Private::to_c(std::make_shared<CV>(std::move(raw)));
}
}

/********************************************************************/
/*                              Create                              */
/********************************************************************/

extern "C" {

// Symbol

ClaricppExpr *claricpp_create_symbol_bool(const char *const name) {
    return Private::to_c(Create::symbol(std::string { name }));
}

/** A local macro used for consistency */
#define CREATE_SYM(TYPE, NAME)                                                                    \
    ClaricppExpr *claricpp_create_symbol_##NAME(const char *const name,                           \
                                                const SIZE_T bit_length) {                        \
        return Private::to_c(Create::symbol<Expression::TYPE>(std::string { name }, bit_length)); \
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
        return Private::to_c(Create::literal(value));                                             \
    }

CREATE_LIT(bool, bool);
CREATE_LIT(char *const, string);
CREATE_LIT(float, float);
CREATE_LIT(double, double);

ClaricppExpr *claricpp_create_literal_vs(const HASH_T hash, const VS_T value,
                                         const SIZE_T bit_length) {
    return Private::to_c(Create::literal(std::make_shared<PyObj::VS>(hash, value, bit_length)));
}

CREATE_LIT(uint8_t, u8);
CREATE_LIT(uint16_t, u16);
CREATE_LIT(uint32_t, u32);
CREATE_LIT(uint64_t, u64);

// @todo : BigInt
// ClaricppExpr * claricpp_create_literal_bv_big_int(const ClaricppBigInt value);

// Cleanup
#undef CREATE_LIT
}
