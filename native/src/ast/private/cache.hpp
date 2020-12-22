/**
 * @file
 * @brief This file defines a generic hash cache type
 */
#ifndef __AST_PRIVATE_CACHE_HPP__
#define __AST_PRIVATE_CACHE_HPP__

#include "../../utils/log.hpp"

#include <algorithm>
#include <map>
#include <memory>
#include <shared_mutex>
#include <type_traits>


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace used to designate certain items in ast as private
     *  These functions should not be called outside of the ast directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** A generic cache class that
         *  This maps a Key to std::weak_ptr<Value>
         *  This class will occassionally gc dead weak_ptr's in the cache
         *  @todo We could have a TLS deletion queue if we want to increase efficiency
         */
        template <typename Hash, typename Cached> class Cache {
          public:
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
                    std::unique_lock<decltype(lock)> rw(lock);
                    // Initial find
                    auto lookup = this->unsafe_find(h);
                    if (lookup != nullptr) {
                        return lookup;
                    }

                } // Unlock

                // Construct our cached
                // We don't know how long this will take so we do it un an unlocked context
                std::shared_ptr<Cached> ret(new Derived(h, std::forward<Args>(args)...));

                // Create locked scope
                {
                    std::unique_lock<decltype(lock)> rw(lock);
                    // Second lookup
                    auto lookup = this->unsafe_find(h);
                    if (lookup != nullptr) {
                        ret.reset();
                        return lookup;
                    }
                    // Add to cache
                    this->cache.emplace(h, ret);
                    // Garbage collection if needed
                    if (this->cache.size() >= this->gc_resize) {
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
            auto unsafe_find(const Hash &h) {
                auto lookup = this->cache.find(h);
                if (lookup != this->cache.end()) {
                    std::shared_ptr<Cached> locked = lookup->second.lock();
                    // If the weak_ptr is valid, return it
                    if (locked) {
                        return locked;
                    }
                    // Otherwise remove it from the cache
                    else {
                        cache.erase(lookup);
                    }
                }

                // If it does not exist, return a pointer to null
                return std::shared_ptr<Cached>(nullptr);
            }

            /** Remove all weak_ptr's in cache that no longer point to a valid object
             *  This function is not thread-safe
             * 	@todo improve logging message
             */
            void unsafe_gc() {
                std::vector<Hash> del;
                Utils::log("Garbage collecting cache");
                // Find all expired weak_ptrs
                for (auto i = this->cache.begin(); i != this->cache.end(); ++i) {
                    if (i->second.expired()) {
                        del.push_back(i->first);
                    }
                }
                // Delete them
                for (typename CacheMap::size_type i = 0; i < del.size(); ++i) {
                    this->cache.erase(del[i]);
                }
                // Resize gc_size
                this->gc_resize = 2 * this->cache.size();
            }

            /************************************************/
            /*                Representation                */
            /************************************************/

            /** The cache representation */
            CacheMap cache;

            /** The size the cache should have weak_ptr's gc'd when it is larger than
             *  Default 1000
             */
            typename CacheMap::size_type gc_resize = 1000;

            /** A mutex used to protect the internal representation */
            std::shared_mutex lock;
        };

    } // namespace Private

} // namespace AST

#endif
