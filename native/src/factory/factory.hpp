/**
 * @file
 * @brief This file defines a generic factory function
 */
#ifndef R_SRC_FACTORY_FACTORY_HPP_
#define R_SRC_FACTORY_FACTORY_HPP_

#include "factory_made.hpp"

#include "../hash.hpp"
#include "../util.hpp"


namespace Factory {

    /** The const shared pointer type that factory returns */
    template <typename T> using Ptr = std::shared_ptr<const T>;

    namespace Private {
        /** The factory cache
         *  Note: This is not a static variable of the factory function because we want
         *  to make it agnostic of cv qualifiers. This also makes testing easier.
         *  Note: For some reason if this is an inline variable rather than a
         *  function linked executables may get an incorrect address when using this.
         */
        template <typename Base> inline auto &gcache() noexcept {
            static Util::WeakCache<Hash::Hash, const Base> cache {};
            return cache;
        }
    } // namespace Private

    /** A factory used to construct subclasses of Base.
     *  Returns a pointer Ptr<Base> that can be static_pointer casted down to Ptr<T> safely
     *  Instantiable subclasses that want to be directly constructed via factory:
     *    1. Must have a static const CUID::CUID static_cuid field (define it by
     *       CUID_DEFINE_MAYBE_UNUSED)
     *    2. Must have each desired usable constructor's first argument be of type const
     *       Hash::Hash& and must pass this argument up to the FactoryMade class
     *	  3. Must include the FACTORY_ENABLE_CONSTRUCTION_FROM_BASE method
     *  Arguments are passed by non-const forwarding reference
     *  @todo update eager_backends functionality
     */
    template <typename Base, typename T, typename... Args>
    inline Ptr<Base> factory(Args &&...args) {
        FactoryMade::static_type_check<Base, T, Args...>();

        // Check to see if the object to be constructed exists in the hash cache
        // Note we cast to apply const to be explicit here, just in case. We need args later!
        const Hash::Hash hash { Hash::hash(T::static_cuid, static_cast<const Args &&>(args)...) };

        // Note: we have these two as distinct statements to ensure hash is done first
        // As the std::forward may move args

        // Use the cv unqualified type as the key
        using CacheKeyT = std::remove_cv_t<Base>;

        // If the Factory::Ptr and Cache::Ptr are not implicitly convertible, this should warn
        return Private::gcache<CacheKeyT>().template find_or_emplace<T>(
            hash, hash, std::forward<Args>(args)...);
    }

    /** Get a shared pointer from a hash
     *  If the object does not exist it returns a shared pointer to nullptr
     */
    template <typename Base> Ptr<Base> find(const Hash::Hash h) {
        using CacheKeyT = std::remove_cv_t<Base>;
        return Private::gcache<CacheKeyT>().find(h);
    }

} // namespace Factory

#endif
