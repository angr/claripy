/**
 * @file
 * @brief This file defines a generic factory function
 */
#ifndef __FACTORY_FACTORY_HPP__
#define __FACTORY_FACTORY_HPP__

#include "factory_made.hpp"

#include "../hash.hpp"
#include "../utils.hpp"


// Forward declarations
struct CUID;

namespace Factory {

    namespace Private {
        /** The factory cache
         *  Note: This is not a static variable of the factory function because
         *  we want to allow classes to declare this, and only this specific cache, as a friend
         */
        template <typename Base> Utils::Cache<Hash::Hash, Base> cache {};
    } // namespace Private

    /** A factory used to construct subclasses of Base.
     *  Instantiable subclasses that want to be directly constructed via factory:
     *    1. Must have a static const Constants::UInt static_cuid field (define it by
     *       DEFINE_STATIC_CUID)
     *    2. Must have each desired usable constructor's first argument be of type const
     *       Hash::Hash& and must pass this argument up to the FactoryMade class
     *	  3. Must include the FACTORY_ENABLE_CONSTRUCTION_FROM_BASE method
     *  Arguments are passed by non-const forwarding reference
     *  @todo update eager_backends functionality
     */
    template <typename Base, typename T, typename... Args>
    inline Constants::SConstPtr<T> factory(Args &&...args) {
        FactoryMade::static_type_check<Base, T, Args...>();

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
