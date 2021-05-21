/**
 * @file
 * @brief Define the simplifications cache and add a method for adding to it
 */
#ifndef R_SIMPLIFICATION_CACHE_HPP_
#define R_SIMPLIFICATION_CACHE_HPP_

#include "../expression.hpp"
#include "../utils.hpp"


namespace Simplification {

    namespace Private {

        /** The simplification cache */
        inline Utils::WeakCache<Hash::Hash, Expression::Base> cache {};

    } // namespace Private

    /** A method for adding to the simplification cache
     *  Record that an Expression with Hash h simplifies to Expression e
     */
    void cache(const Hash::Hash h, const Expression::BasePtr &e) { Private::cache.insert(h, e); }

} // namespace Simplification

#endif
