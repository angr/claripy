/**
 * @file
 * @brief This file defines Expression factory functions
 */
#ifndef __EXPRESSION_FACTORY_HPP__
#define __EXPRESSION_FACTORY_HPP__

#include "cast.hpp"
#include "private/factory_cache.hpp"
#include "private/raw.hpp"

#include "../utils.hpp"


namespace Expression {

    /** A factory used to construct subclasses of Expression::Raw::Type::Base. Arguments are
     *  consumed. This function takes in move references for everything; it has no const
     *  promises, it may consume anything that is passed to it. This factory handles hashing
     *  and returns an Expression::Base (a shared pointer to the constructed object)
     *  @todo update eager_backends functionality
     */
    template <typename T, typename... Args> T factory(Args &&...args) {

        // Deduce the Expression::Raw::Type type the shared pointer type T contains
        using RawT = Private::Raw<T>;

        // Compile time error checking
        static_assert(std::is_same<std::shared_ptr<RawT>, T>::value, "T must be a shared pointer");
        static_assert(std::is_base_of<Raw::Type::Base, RawT>::value,
                      "T must derive from Expression::Cached::Base");

        // Check to see if the object to be constructed exists in the hash cache
        // We run hash vis run_cr_function to ensure args are passed by const reference
        const Hash h = Utils::run_cr_function(hash<RawT>, args...);
        auto base_ptr =
            Private::factory_cache.find_or_emplace<RawT>(h, std::forward<Args>(args)...);
        return down_cast_throw_on_fail<T>(base_ptr);
    }

} // namespace Expression

#endif
