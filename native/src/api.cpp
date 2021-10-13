/** @file */
// #include "api.h"

#include "annotation.hpp"
#include "backend.hpp"
#include "create.hpp"
#include "py_obj.hpp"
#include "simplification.hpp"
#include "utils.hpp"


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
        thread_local Utils::ToHeapCache<Expression::BasePtr> expression_heap_cache {};

        Create::EBasePtr claricpp_abs_helper(Constants::CTSC<AnPtrPtr> annotations,
                                             const Constants::UInt size,
                                             Constants::CTSC<Create::EBasePtr> x) {
            const auto sx { *x };
            if (size == 0) {
                return Create::abs(sx);
            }
            else {
                Annotation::Vec::RawVec vec;
                vec.reserve(size);
                for (Constants::UInt i { 0 }; i < size; ++i) {
                    vec.emplace_back(*(annotations[i]));
                }
                return Create::abs(sx, std::make_shared<Annotation::Vec>(std::move(vec)));
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

} // namespace C_API