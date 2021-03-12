/**
 * @file
 * @brief This file defines the C API of claricpp
 */
#ifndef __API_HPP__
#define __API_HPP__

#include "constants.hpp"
#include "create.hpp"
#include "expression/base.hpp"
#include "utils/log/log.hpp"

#include <exception>
#include <memory>


namespace C_API {

    namespace Private {
        /** Expression heap cache */
        thread_local HeapCache<Expression::BasePtr> expression_heap_cache {};
    }; // namespace Private

    /** Enfore compatability with the C ABI
     *  Note: Defining extern "C" within a namespace defines the functions
     *  both within and outside of the namesapce
     */
    extern "C" {

    /** For freeing expressions */
    void claricpp_expression_destructor(Expression::BasePtr *const ptr) {
        Private::expression_heap_cache.free(ptr);
    }

    /* Create::EBasePtr * claricpp_abs(const Annotation::BasePtr>* ans[], const Constants::UInt
     * size, const EBasePtr * x) { */
    /* 	return expression_heap_cache.move_to_heap(Create::abs(std::vector<Annotation::BasePtr{ans,
     * size}, x)); */
    /* } */
    }

} // namespace C_API

#endif
