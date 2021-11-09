/**
 * @file
 * @brief Define the simplifications cache and add a method for adding to it
 */
#ifndef R_SIMPLIFICATION_CACHE_HPP_
#define R_SIMPLIFICATION_CACHE_HPP_

#include "../expr.hpp"
#include "../util.hpp"


namespace Simplification {

    namespace Private {

        /** The simplification cache */
        inline Util::WeakCache<Hash::Hash, Expr::Base> cache {};

    } // namespace Private

    /** A method for adding to the simplification cache
     *  Record that an Expr with Hash h simplifies to non-null Expr pointer e
     */
    inline void cache(const Hash::Hash h, const Expr::BasePtr &e) {
        UTIL_AFFIRM_NOT_NULL_DEBUG(e);
        Private::cache.insert(h, e);
    }

} // namespace Simplification

#endif
