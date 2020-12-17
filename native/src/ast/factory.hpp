/**
 * @file
 * @brief This file defines the AST::factory function
 */
#ifndef __AST_FACTORY_HPP__
#define __AST_FACTORY_HPP__

#include "base.hpp"
#include "hash_cache.hpp"

#include "../errors/unexpected.hpp"

#include <memory>
#include <utility>


/** A namespace used for the ast directory */
namespace AST::Cached {

    /** A factory used to construct subclasses of AST::Cached::Base. This consumes its arguments
     *  This function takes in move references for everything; it has no const promises, it may
     * consume anything that is passed to it. This factory handles hashing and returns an AST::Base
     * (a shared pointer to the constructed object)
     *  @todo This will probably want to take in args via move
     */
    template <class T, typename... Args>
    T factory(std::set<BackendID> &&eager_backends, Args &&...args) {

        // Deduce the AST::Cached type the shared pointer type T contains
        using Internal = decltype(std::declval<T>().get());
        using CachedT = typename std::remove_pointer<Internal>::type;

        // Compile time error checking
        static_assert(std::is_convertible<CachedT *, AST::Cached::Base *>::value,
                      "T must derive from AST::Cached::Base");

        // Check to see if the object to be constructed exists in the hash cache
        const Hash h = CachedT::hash(args...);
        auto lookup = Private::hash_cache.find(h);

        // If it already exists in the hash cache
        if (lookup != Private::hash_cache.end()) {
            ::AST::Base locked = lookup->second.lock();
            // If the weak_ptr is valid, return it
            if (locked) {
                T possible_ret = std::dynamic_pointer_cast<CachedT>(locked);
                if (possible_ret) {
                    return possible_ret;
                }
                // This should never happen unless we have a hash collision or a coding error
                else {
                    Errors::Unexpected::BadCast(__FILE__ ": " MACRO_TO_STRING(
                        __LINE__) ": dynamic_pointer_cast within AST::factory failed.");
                }
            }
            // Otherwise remove it from the cache
            else {
                Private::hash_cache.erase(lookup);
            }
        }

        // Since no cached object exists, construct one, cache it, then return it
        T ret = T(new CachedT(h, std::forward<Args>(args)...));
        Private::hash_cache[h] = std::weak_ptr<CachedT>(ret);
        return ret;
    }

} // namespace AST::Cached

/** A namespace used for the ast directory */
namespace AST {

    /** A alias for AST::Cached::Factory
     *  The compilers should optiize away this call
     *  @todo remove the need for this
     */
    template <class T, typename... Args>
    inline T factory(std::set<BackendID> &&eager_backends, Args &&...args) {
        return Cached::factory<T, Args...>(std::forward<std::set<BackendID>>(eager_backends),
                                           std::forward<Args>(args)...);
    }

} // namespace AST

#endif
