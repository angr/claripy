/**
 * @file
 * @brief This file defines AST factory functions
 */
#ifndef __AST_FACTORY_HPP__
#define __AST_FACTORY_HPP__

#include "cast.hpp"
#include "private/factory_cache.hpp"
#include "private/raw.hpp"

#include <memory>
#include <utility>


namespace AST {

    /** A factory used to construct subclasses of AST::RawTypes::Base. Arguments are consumed.
     *  This function takes in move references for everything; it has no const promises,
     *  it may consume anything that is passed to it. This factory handles hashing and
     *  returns an AST::Base (a shared pointer to the constructed object)
     *  @todo update eager_backends functionality
     */
    template <typename T, typename... Args>
    T factory(std::set<BackendID> &&eager_backends, Args &&...args) {
        (void) eager_backends;

        // Deduce the AST::RawTypes type the shared pointer type T contains
        using RawT = Private::Raw<T>;

        // Compile time error checking
        static_assert(std::is_same<std::shared_ptr<RawT>, T>::value, "T must be a shared pointer");
        static_assert(std::is_base_of<RawTypes::Base, RawT>::value,
                      "T must derive from AST::Cached::Base");

        // Check to see if the object to be constructed exists in the hash cache
        const Hash h = RawT::hash(args...);
        auto base_ptr =
            Private::factory_cache.find_or_emplace<RawT>(h, std::forward<Args>(args)...);
        return down_cast_throw_on_fail<T>(base_ptr);
    }

} // namespace AST

#endif
