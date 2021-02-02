/**
 * @file
 * @brief This file defines the OP factory
 */
#ifndef __OP_FACTORY_HPP__
#define __OP_FACTORY_HPP__

#include "base.hpp"

#include "../hash.hpp"
#include "../utils.hpp"

#include <memory>


namespace Op {

    namespace Private {
        /** The factory cache */
        inline Utils::Cache<Hash::Hash, Base> cache {};
    } // namespace Private

    /** A factory used to construct subclasses of Expression::Raw::Base. Arguments are
     *  consumed. This function takes in move references for everything; it has no const
     *  promises, it may consume anything that is passed to it. This factory handles hashing
     *  and returns an Expression::Base (a shared pointer to the constructed object)
     *  @todo update eager_backends functionality
     */
    template <typename T, typename... Args>
    inline Constants::SPtr<const T> factory(Args &&...args) {
        static_assert(std::is_base_of_v<Base, T>, "T must derive from SOC::Base");

        // Check to see if the object to be constructed exists in the hash cache
        const Hash::Hash hash { Hash::hash(static_cast<const Args>(args)...) };

        // Note: we have these two as distinct statements to ensure hash is done first
        // As the std::forward may move args

#ifndef DEBUG
        // Since cache emplaces a T, this is a safe static cast
        return std::static_pointer_cast<const T>(
#else
        // Since cache emplaces a T, this is a safe static cast
        return Utils::dynamic_pointer_cast_throw_on_fail<const T>(
#endif
            // Cache lookup based on hash
            Private::cache.find_or_emplace<T>(hash, std::forward<Args>(args)...));
    }

} // namespace Op

#endif
