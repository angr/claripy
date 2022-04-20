/**
 * @file
 * \ingroup util
 * @brief A cached way of copying data to the heap
 */
#ifndef R_SRC_UTIL_HEAPCACHE_HPP_
#define R_SRC_UTIL_HEAPCACHE_HPP_

#include "log.hpp"
#include "safe_alloc.hpp"

#include "../constants.hpp"
#include "../macros.hpp"
#include "../unittest.hpp"

#include <cstdlib>
#include <vector>


namespace Util {

    /** A heap cache for objects of type T */
    template <typename T> class HeapCache {
        ENABLE_UNITTEST_FRIEND_ACCESS
      public:
        /** Constructor */
        inline HeapCache() { reserve(); }

        /** Move x onto the heap */
        inline T *move_to_heap(T &&x) {
            // Construct our new T on pop()'s memory
            // std::launder is not needed here since we do not have any aliases
            return new (pop()) T { std::move(x) }; // NOLINT
        }

        /** Construct a T on the heap */
        template <typename... Args> inline T *emplace_on_heap(Args &&...args) {
            return new (pop()) T { std::forward<Args>(args)... };
        }

        /** Reclaim the memory pointed to by non-null pointer x, calls x's destructor */
        inline void free(T *const x) {
            UTIL_ASSERT_NOT_NULL_DEBUG(x);
            x->~T(); // Destruct x
            data.emplace_back(x);
        }

        /** Save space by freeing extra cache items */
        inline void downsize() {
            Util::Log::info("HeapCache: downsizing");
            if (data.size() <= dsize) {
                return;
            }
            for (auto i { dsize }; i < data.size(); ++i) {
                std::free(data[i]);
            }
            data.resize(dsize);
        }

      private:
        /** Disable implicits */
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(HeapCache, delete);

        /** The allocation method */
        inline T *alloc() noexcept { return Safe::malloc<T>(1); }

        /** Expand data to a size of at least dsize
         *  This will *not* shrink the data
         */
        inline void reserve() {
            if (data.size() >= dsize) {
                return;
            }
            data.reserve(dsize); // Can throw if max_length is exceeded
            const auto diff { dsize - data.size() };
            for (U64 i { 0 }; i < diff; ++i) {
                data.emplace_back(alloc());
            }
        }

        /** Pop an item from the cache for use */
        inline T *pop() {
            if (data.size() > 0) {
                T *const ret { data.back() };
                data.pop_back();
                return ret;
            }
            reserve();
            return alloc();
        }

        // Representation

        /** The size reserve will use */
        static const constexpr U64 dsize { 0x1000 };

        /** Internal data storage */
        std::vector<T *> data {};

        /** Error checking */
        static_assert(sizeof(U64) == sizeof(typename decltype(data)::size_type),
                      "CHeapCache size type assumptions are invalid.");
    };

} // namespace Util

#endif
