/**
 * @file
 * @brief This file defines the AST::factory function
 */
#ifndef __AST_FACTORY_HPP__
#define __AST_FACTORY_HPP__

#include "cast.hpp"
#include "private/cache.hpp"
#include "private/raw.hpp"
#include "raw_types/base.hpp"

#include "../errors/unexpected.hpp"

#include <memory>
#include <utility>


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace used to designate certain items in ast as private
     *  These functions should not be called outside of the ast directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** Define a cache the AST factory can use */
        extern Private::Cache<Hash, RawTypes::Base> cache;

    } // namespace Private

    /** A namespace which contains the raw AST types that are constructed via AST::factory
     *  These classes are unlikely to be accessed directly, but rather should be via a shared_ptr
     */
    namespace RawTypes {
        /** A factory used to construct subclasses of AST::RawTypes::Base. This consumes its
         * arguments This function takes in move references for everything; it has no const
         * promises, it may consume anything that is passed to it. This factory handles hashing and
         * returns an AST::Base (a shared pointer to the constructed object)
         *  @todo This will probably want to take in args via move
         *  @todo update eager_backends functionality
         */
        template <typename T, typename... Args>
        T factory(std::set<BackendID> &&eager_backends, Args &&...args) {
            (void) eager_backends;

            // Deduce the AST::RawTypes type the shared pointer type T contains
            using RawT = Private::Raw<T>;

            // Compile time error checking
            static_assert(std::is_same<std::shared_ptr<RawT>, T>::value,
                          "T must be a shared pointer");
            static_assert(std::is_base_of<AST::RawTypes::Base, RawT>::value,
                          "T must derive from AST::Cached::Base");

            // Check to see if the object to be constructed exists in the hash cache
            const Hash h = RawT::hash(args...);
            auto base_ptr = Private::cache.lookup_or_emplace<RawT>(h, std::forward<Args>(args)...);
            return ::AST::down_cast_throw_on_fail<T>(base_ptr);
        }

    } // namespace RawTypes

    /** A alias for AST::Cached::Factory
     *  The compilers should optiize away this call
     *  @todo remove the need for this
     */
    template <typename T, typename... Args>
    inline T factory(std::set<BackendID> &&eager_backends, Args &&...args) {
        return RawTypes::factory<T, Args...>(std::forward<std::set<BackendID>>(eager_backends),
                                             std::forward<Args>(args)...);
    }

} // namespace AST

#endif
