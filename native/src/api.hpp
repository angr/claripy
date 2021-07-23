/**
 * @file
 * @brief This file defines the C API of claricpp
 */
#ifndef R_API_HPP_
#define R_API_HPP_

#include <memory>


// Forward declarations
namespace Expression {
    class Base;
    using BasePtr = std::shared_ptr<const Base>;
} // namespace Expression


namespace C_API {

    namespace Private {
        /** Expression heap cache */
        thread_local HeapCache<Expression::BasePtr> expression_heap_cache {};
    }; // namespace Private

    /** Annotation base pointer pointer abbreviation */
    using AnPtr = Annotation::BasePtr *;

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
    Create::EBasePtr *claricpp_abs(const AnPtr *annotations, const Constants::UInt size,
                                   const EBasePtr *x) {
        return expression_heap_cache.move_to_heap(
            Create::abs(std::vector < Annotation::BasePtr { ans, ans + size }, x));
    }
    }

} // namespace C_API

#endif
