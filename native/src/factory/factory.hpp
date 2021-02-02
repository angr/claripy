/**
 * @file
 * @brief This file defines a generic factory function
 */
#ifndef __FACTORY_FACTORY_HPP__
#define __FACTORY_FACTORY_HPP__

#include "has_static_cuid.hpp"

#include "../hash.hpp"
#include "../utils.hpp"

#include <memory>
#include <type_traits>


namespace Factory {


    namespace Private {
        /** The factory cache */
        template <typename Base> Utils::Cache<Hash::Hash, Base> cache {};
    } // namespace Private

    /** A factory used to construct subclasses of Base.
     *  T must have a static_cuid and be instantiable
     *  Arguments are consumed.
     *  @todo update eager_backends functionality
     */
    template <typename Base, typename T, typename... Args>
    inline Constants::SConstPtr<T> factory(Args &&...args) {
        static_assert(has_static_cuid_v<T>,
                      "Factory cannot construct anything without a static_cuid");
        static_assert(std::is_same_u<Constants::UInt, T::static_cuid>,
                      "T::static_cuid must be of type Constants::UInt");
        static_assert(std::is_base_of_v<Base, T>, "T must derive from Base");

        // Check to see if the object to be constructed exists in the hash cache
        const Hash::Hash hash { Hash::hash(T::static_cuid, static_cast<const Args>(args)...) };

        // Note: we have these two as distinct statements to ensure hash is done first
        // As the std::forward may move args

        const auto ret { Private::cache<Base>.template find_or_emplace<T>(
            hash, std::forward<Args>(args)...) };
        if constexpr (std::is_same_v<Base, T>) {
            return ret;
        }
        else {
            // Since cache emplaces a T, this is a safe static cast
            return Utils::static_down_cast<const T>(ret);
        }
    }

} // namespace Factory

#endif
