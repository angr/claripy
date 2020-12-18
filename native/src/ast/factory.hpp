/**
 * @file
 * @brief This file defines the AST::factory function
 */
#ifndef __AST_FACTORY_HPP__
#define __AST_FACTORY_HPP__

#include "base.hpp"
#include "cache.hpp"
#include "cast.hpp"

#include "../errors/unexpected.hpp"

#include <memory>
#include <utility>


// We are defining factory in the Cached namespace of AST
/** A namespace used for the ast directory */
namespace AST {

    /** A namespace used to designate certain items in ast as private
     *  These functions should not be called outside of the ast directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** Define a cache the AST factory can use */
        Private::Cache<Hash, Cached::Base> cache;

    } // namespace Private

    /** A namespace which contains self-caching classes and things related to AST caching
     *  These classes are unlikely to be accessed directly, but rather should be accessed via a
     * shared_ptr
     */
    namespace Cached {
        /** A factory used to construct subclasses of AST::Cached::Base. This consumes its
         * arguments This function takes in move references for everything; it has no const
         * promises, it may consume anything that is passed to it. This factory handles hashing and
         * returns an AST::Base (a shared pointer to the constructed object)
         *  @todo This will probably want to take in args via move
         */
        template <typename T, typename... Args>
        T factory(std::set<BackendID> &&eager_backends, Args &&...args) {

            // Deduce the AST::Cached type the shared pointer type T contains
            using CachedT = decltype(Private::cache)::Internal<T>;

            // Compile time error checking
            static_assert(std::is_same<std::shared_ptr<CachedT>, T>::value,
                          "T must be a shared pointer");
            static_assert(std::is_base_of<AST::Cached::Base, CachedT>::value,
                          "T must derive from AST::Cached::Base");

            // Check to see if the object to be constructed exists in the hash cache
            const Hash h = CachedT::hash(args...);
            auto base_ptr =
                Private::cache.lookup_or_emplace<CachedT>(h, std::forward<Args>(args)...);
            return ::AST::cast<CachedT>(base_ptr);
        }

    } // namespace Cached

    /** A alias for AST::Cached::Factory
     *  The compilers should optiize away this call
     *  @todo remove the need for this
     */
    template <typename T, typename... Args>
    inline T factory(std::set<BackendID> &&eager_backends, Args &&...args) {
        return Cached::factory<T, Args...>(std::forward<std::set<BackendID>>(eager_backends),
                                           std::forward<Args>(args)...);
    }


} // namespace AST

#endif
