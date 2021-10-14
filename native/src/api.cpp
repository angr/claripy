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
    template <typename In, typename Out = Map<In>> static inline Out *to_c(In &&x) {
        static thread_local Utils::CHeapCache<In, Out> cache {};
        return cache.move_to_heap(std::forward<In>(x));
    }
} // namespace Private

/********************************************************************/
/*                            Annotation                            */
/********************************************************************/

extern "C" {

/** Return a new Annotation::Base */
ClaricppAnnotation *claricpp_annotation_new_base() {
    return Private::to_c(Annotation::factory<Annotation::Base>());
}

/** Return a new Annotation::SimplificationAvoidance */
ClaricppAnnotation *claricpp_annotation_new_simplification_avoicance() {
    return Private::to_c(Annotation::factory<Annotation::SimplificationAvoidance>());
}
/** Create an Expression::SPAV from a list of annotations */
// ClaricppSPAV * claricpp_annotation_create_spav() {
// }
}

#if 0
// Forward declarations
namespace Expression {
class Base;
using BasePtr = std::shared_ptr<const Base>;
} // namespace Expression


namespace C_API {

/** Annotation base pointer pointer abbreviation */
using AnPtrPtr = Annotation::BasePtr *;

namespace Private {
    /** Expression heap cache */
    thread_local Utils::CHeapCache<Expression::BasePtr> expression_heap_cache {};

    Create::EBasePtr claricpp_abs_helper(Constants::CTSC<AnPtrPtr> annotations,
                                         const Constants::UInt size,
                                         Constants::CTSC<Create::EBasePtr> x) {
        if (size == 0) {
            return Create::abs(*x);
        }
        else {
            Annotation::Vec::RawVec vec;
            vec.reserve(size);
            for (Constants::UInt i { 0 }; i < size; ++i) {
                vec.emplace_back(*(annotations[i]));
            }
            return Create::abs(*x, std::make_shared<Annotation::Vec>(std::move(vec)));
        }
    }

}; // namespace Private

/** Enforce compatability with the C ABI
 *  Note: Defining extern "C" within a namespace defines the functions
 *  both within and outside of the namespace
 */
extern "C" {

/** For freeing expressions */
void claricpp_expression_destructor(Expression::BasePtr *const ptr) {
    Private::expression_heap_cache.free(ptr);
}

/** Create an ABS Expression with arguments: x
 *  @param annotations: An array of size AnPtrs
 *  @param size: The number of elements in annotations
 *  @param x: The operand to ABS
 */
Create::EBasePtr *claricpp_abs(Constants::CTSC<AnPtrPtr> annotations,
                               const Constants::UInt size,
                               Constants::CTSC<Create::EBasePtr> x) {
    return Private::expression_heap_cache.move_to_heap(
        Private::claricpp_abs_helper(annotations, size, x));
}
}
#endif