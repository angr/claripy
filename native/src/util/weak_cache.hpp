/**
 * @file
 * \ingroup util
 * @brief This file defines a generic hash cache type
 */
#ifndef R_SRC_UTIL_WEAKCACHE_HPP_
#define R_SRC_UTIL_WEAKCACHE_HPP_

#include "err.hpp"
#include "log.hpp"
#include "make_derived_shared.hpp"
#include "max.hpp"
#include "pointer_cast.hpp"
#include "pow.hpp"

#include "../unittest.hpp"

#include <algorithm>
#include <map>
#include <shared_mutex>


namespace Util {

    /** A generic thread-safe cache class that
     *  This maps a Key to std::weak_ptr<const Cached>
     *  This class will occasionally gc dead weak_ptr's in the cache
     *  @todo We could have a TLS deletion queue if we want to increase efficiency
     */
    template <typename Hash, typename Cached> class WeakCache final {
        ENABLE_UNITTEST_FRIEND_ACCESS

        /** The pointer type publicly exposed */
        using Ptr = std::shared_ptr<const Cached>;

        /** Abbreviate the type this is */
        using Self = WeakCache<Hash, Cached>;

        // Disable most implicits
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(WeakCache, delete);

      public:
        /** Default constructor */
        WeakCache() = default;

        // Enable custom logging
        UTIL_LOG_ENABLE_CUSTOM_LOGGING("HashCache")

        /** The type of the cache used internally */
        using CacheMap = std::map<Hash, std::weak_ptr<const Cached>>;

        /** Return true if the object is within the cache, else false
         *  This function is thread-safe
         */
        bool exists(const Hash &h) { return find(h); }

        /** If h is in the cache, return a shared pointer to it
         *  Otherwise return a shared pointer to nullptr
         *  This function is thread-safe
         */
        Ptr find(const Hash &h) {
            std::unique_lock<decltype(m)> rw(m);
            return unsafe_find(h);
        }

        /** Insert a new entry into the cache
         *  This function is thread-safe
         */
        void insert(const Hash &h, const std::shared_ptr<const Cached> &c) {
            std::unique_lock<decltype(m)> rw(m);
            cache.insert(h, c);
        }

        /** Add an entry into the cache (will overwrite existing entries)
         *  This function is thread-safe
         */
        void put(const Hash &h, const std::shared_ptr<const Cached> &c) {
            std::unique_lock<decltype(m)> rw(m);
            cache[h] = c;
        }

        /** If hash h is not in the cache, construct a Cached from the given args
         *  Return a shared pointer to the newly constructed Cached, and cache it
         *  This function is thread-safe
         *  Note: For performance reasons, we do not lock our cache between checking if the
         *  Hash h is in our cache and constructing our Cached, thus there is a chance the
         *  Cached may be constructed and during its construction another thread may have added
         *  h to our cache. In this case, we delete our newly constructed object and return a
         *  shared_pointer to the Cached that the other thread emplaced. Note that the given
         *  arguments are passed via move operations and may be consumed.
         *  @param h: The hash our cache uses as a key
         *  @param args: The arguments given to Cached's constructor
         */
        template <typename Derived, typename... Args>
        Ptr find_or_emplace(const Hash &h, Args &&...args) {

            // Static check
            static_assert(Type::Is::ancestor<Cached, Derived>,
                          "Derived must derive from Cached or be a Cached");

            // Initial cache lookup
            if (const auto lookup { find(h) }; lookup) {
                return lookup;
            }

            // Construct our object to be cached
            // We don't know how long the constructor will take so we do it in an unlocked context
            Ptr ret {
                // Pointer up cast
                Util::PCast::Static::up<const Cached>(
                    // Construct this before casting to avoid slicing
                    // It also avoids the need for a custom deleter to deal with access controls
                    std::shared_ptr<const Derived> {
                        // We use new because make_shared might not have access permissions
                        new Derived { std::forward<Args>(args)... } })
            };

            // Create locked scope
            {
                std::unique_lock<decltype(m)> rw(m);
                // Second lookup
                if (const auto lookup { unsafe_find(h) }; lookup) {
                    return lookup;
                }
                // Add to cache
#ifdef DEBUG
                auto &&[_, success] = cache.emplace(h, ret);
                UTIL_ASSERT(Err::Unknown, success,
                            "Cache emplacement failed after verifying item not already in cache.");
#else
                (void) cache.emplace(h, ret);
#endif
                // Garbage collection if needed
                if (cache.size() > gc_resize) {
                    unsafe_gc();
                }

            } // Unlock

            // Return the shared pointer
            return ret;
        }

      private:
        /** A non-threadsafe find function for the cache
         *  On success returns a shared pointer to the value
         *  On failure, returns a null shared pointer
         */
        Ptr unsafe_find(const Hash &h) {
            if (auto lookup { cache.find(h) }; lookup != cache.end()) {
                const auto &weak { lookup->second };
                // If the weak_ptr is valid, return it
                if (not weak.expired()) { // Do not waste cycles with .lock() if not needed
                    if (auto locked { weak.lock() }; locked) {
                        return locked;
                    }
                }
                // Else remove it from the cache
                cache.erase(lookup);
            }
            // If it does not exist, return a pointer to null
            return { nullptr };
        }

        /** Remove all std::weak_ptr's in cache that no longer point to a valid object
         *  This function is not thread-safe
         */
        void unsafe_gc() {
            std::vector<Hash> del;
            Log::debug<Self>("Garbage collecting cache");
            // Find all expired weak_ptrs
            for (const auto &[hash, ptr] : cache) {
                if (ptr.expired()) {
                    del.emplace_back(hash);
                }
            }
            // Delete them
            Log::verbose<Self>(__func__, ": Cache invalidation of ", del.size(), " items.");
            for (const auto i : del) {
                cache.erase(i);
            }
            // Resize gc_size to a reasonable size
            gc_resize = Max::value(gc_resize_default, cache.size() << 1);
            Log::debug<Self>("Garbage collection complete.");
        }

        /************************************************/
        /*                Representation                */
        /************************************************/

        /** A mutex used to protect the internal representation */
        std::mutex m;

        /** The cache representation */
        CacheMap cache {};

        /** The size the cache should have std::weak_ptr's gc'd when it is larger than */
        typename CacheMap::size_type gc_resize { gc_resize_default };

        /** The default value for gc_resize */
        static const constexpr typename CacheMap::size_type gc_resize_default { pow(2, 10u) - 1 };
    };

} // namespace Util

#endif
