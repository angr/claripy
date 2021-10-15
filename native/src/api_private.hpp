/**
 * @file
 * @brief This defines types which should be opaque to the API
 * This file should not be included by api.h
 */
#ifndef R_APIPRIVATE_HPP_
#define R_APIPRIVATE_HPP_

#include "annotation.hpp"
#include "backend.hpp"
#include "create.hpp"
#include "py_obj.hpp"
#include "simplification.hpp"
#include "utils.hpp"

/********************************************************************/
/*                            extern "C"                            */
/********************************************************************/

// These types should be structs which contain only a single shared pointer named ptr
extern "C" {

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
/*                               C++                                */
/********************************************************************/

namespace API {

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
    } // namespace Private

    /** A shortcut used to access InternalMap */
    template <typename T> using Map = typename Private::InternalMap<T>::Result;

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

} // namespace API

#endif
