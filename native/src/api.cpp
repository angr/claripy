/** @file */
extern "C" {
#include "api.h"
}

#include "annotation.hpp"
#include "backend.hpp"
#include "create.hpp"
#include "py_obj.hpp"
#include "simplification.hpp"
#include "utils.hpp"


/********************************************************************/
/*                        Type Declarations                         */
/********************************************************************/

static_assert(std::is_same_v<SIZE_T, Constants::UInt>, "SIZE_T needs to be changed");

extern "C" {

// These types should be structs which contain only a single shared pointer named ptr

struct ClaricppAnnotation final {
    Annotation::BasePtr ptr;
};

struct ClaricppSPAV final {
    Annotation::SPAV ptr;
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