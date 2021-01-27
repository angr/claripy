/**
 * @file
 * @brief This file defines a generic hash cache type
 */
#ifndef __UTILS_CACHE_HPP__
#define __UTILS_CACHE_HPP__

#include "log.hpp"
#include "max.hpp"
#include "pow.hpp"

#include "../unittest.hpp"

#include <algorithm>
#include <map>
#include <memory>
#include <shared_mutex>
#include <type_traits>


namespace Utils {

    /** A generic cache class that
     *  This maps a Key to std::weak_ptr<Value>
     *  This class will occassionally gc dead weak_ptr's in the cache
     *  @todo We could have a TLS deletion queue if we want to increase efficiency
     */
    template <typename Hash, typename Cached> class Cache {
        ENABLE_UNITTEST_FRIEND_ACCESS

        /** Abbreviate the type this is */
        using Self = Cache<Hash, Cached>;

      public:
        // Enable custom logging
        UTILS_LOG_ENABLE_CUSTOM_LOGGING("HashCache")

        /** The type of the cache used internally */
        using CacheMap = std::map<Hash, std::weak_ptr<Cached>>;

        /** If hash h is not in the cache, construct a Cached from the given args
         *  Return a shared pointer to the newly constructed Cached, and cache it
         *  This function is thread-safe
         *  Note: For performance reasons, we do not lock our cache between checking if the
         * Hash h is in our cache and constructing our Cached, thus there is a chance the
         * Cached may be constructed and during its construction another thread may have added
         * h to our cache. In this case, we delete our newly constructed object and return a
         * shared_pointer to the Cached that the other thread emplaced. Note that the given
         * arguments are passed via move operations and may be consumed.
         * @param h: The hash our cache uses as a key
         * @param args: The arguments given to Cached's constructor
         */
        template <typename Derived, typename... Args>
        std::shared_ptr<Cached> find_or_emplace(const Hash &h, Args &&...args) {
            // Static check
            static_assert(std::is_base_of<Cached, Derived>::value,
                          "Derived must derive from Base");

            // Create locked scope
            {
                std::lock_guard<decltype(lock)> rw(lock);
                // Initial find
                if (auto lookup = this->unsafe_find(h); lookup != nullptr) {
                    return lookup;
                }

            } // Unlock

            // Construct our cached
            // We don't know how long this will take so we do it un an unlocked context
            std::shared_ptr<Cached> ret(new Derived(h, std::forward<Args>(args)...));

            // Create locked scope
            {
                std::lock_guard<decltype(lock)> rw(lock);
                // Second lookup
                if (auto lookup = this->unsafe_find(h); lookup != nullptr) {
                    ret.reset();
                    return lookup;
                }
                // Add to cache
                this->cache.emplace(h, ret);
                // Garbage collection if needed
                if (this->cache.size() > this->gc_resize) {
                    this->unsafe_gc();
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
        std::shared_ptr<Cached> unsafe_find(const Hash &h) {
            if (auto lookup = this->cache.find(h); lookup != this->cache.end()) {
                std::shared_ptr<Cached> locked = lookup->second.lock();
                // If the weak_ptr is valid, return it
                if (locked) {
                    return locked;
                }
                // Otherwise remove it from the cache
                else {
                    cache.erase(lookup);
                    Log::verbose<Self>(__func__, ": Cache invalidation");
                    return std::shared_ptr<Cached>(nullptr);
                }
            }

            // If it does not exist, return a pointer to null
            return std::shared_ptr<Cached>(nullptr);
        }

        /** Remove all std::weak_ptr's in cache that no longer point to a valid object
         *  This function is not thread-safe
         */
        void unsafe_gc() {
            std::vector<Hash> del;
            Log::debug<Self>("Garbage collecting cache");
            // Find all expired weak_ptrs
            for (const auto &[hash, ptr] : this->cache) {
                if (ptr.expired()) {
                    del.push_back(hash);
                }
            }
            // Delete them
            for (const typename CacheMap::size_type i : del) {
                Log::verbose<Self>(__func__, ": Cache invalidation");
                this->cache.erase(i);
            }
            // Resize gc_size to a reasonable size
            this->gc_resize = Max::value(Self::gc_resize_default, this->cache.size() << 1);
            Log::verbose<Self>("Garbage collection complete.");
        }

        /************************************************/
        /*                Representation                */
        /************************************************/

        /** A mutex used to protect the internal representation */
        std::shared_mutex lock;

        /** The cache representation */
        CacheMap cache;

        /** The size the cache should have std::weak_ptr's gc'd when it is larger than */
        typename CacheMap::size_type gc_resize = gc_resize_default;

        /** The default value for gc_resize */
        static const constexpr typename CacheMap::size_type gc_resize_default = pow(2, 10u) - 1;
    };

} // namespace Utils

#endif
