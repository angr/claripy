/**
 * @file
 * @brief This file defines a generic factory function
 */
#ifndef __FACTORY_FACTORY_HPP__
#define __FACTORY_FACTORY_HPP__

#include "factory_made.hpp"

#include "../hash.hpp"
#include "../utils.hpp"


namespace Factory {

    /** The const shared pointer type that factory returns */
    template <typename T> using Ptr = std::shared_ptr<const T>;

    namespace Private {
        /** The factory cache
         *  Note: This is not a static variable of the factory function because
         *  we want to to make it agnostic of cv qualifiers
         *  It also makes testing easier
         */
        template <typename Base> Utils::Cache<Hash::Hash, const Base> inline cache {};
    } // namespace Private

    /** A factory used to construct subclasses of Base.
     *  Returns a pointer Ptr<Base> that can be static_pointer casted down to Ptr<T> safely
     *  Instantiable subclasses that want to be directly constructed via factory:
     *    1. Must have a static const CUID::CUID static_cuid field (define it by
     *       CUID_DEFINE_MAYBE_UNUSUED)
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
        const Hash::Hash hash { Hash::hash(T::static_cuid, static_cast<const Args>(args)...) };

        // Note: we have these two as distinct statements to ensure hash is done first
        // As the std::forward may move args

        // Use the cv unqualified type as the key
        using CacheKeyT = std::remove_cv_t<Base>;

        // If the Factory::Ptr and Cache::Ptr are not implicitly convertible, this should warn
        return Private::cache<CacheKeyT>.template find_or_emplace<T>(hash, hash,
                                                                     std::forward<Args>(args)...);
    }

    /** Return true if the given hash is in the factory cache
     *  This is exposed for optimization reasons; it allows objects to invoke this to check
     *  if something is cached ratehr than store a weak pointer to the factory pointer returned
     */
    template <typename Base> bool in_cache(const Hash::Hash h) {
        return Private::cache<Base>.exists(h);
    }

} // namespace Factory

#endif
