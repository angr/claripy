/**
 * @file
 * \ingroup utils
 * @brief A cached way of copying data to the heap
 */
#ifndef R_UTILS_TOHEAPCACHE_HPP_
#define R_UTILS_TOHEAPCACHE_HPP_

#include "error/unexpected.hpp"
#include "log.hpp"

#include "../constants.hpp"
#include "../macros.hpp"
#include "../unittest.hpp"

#include <cstdlib>
#include <vector>


namespace Utils {

    /** A heap cache for objects of type T
     *  This is used to move stack objects onto the heap
     */
    template <typename T> class ToHeapCache {
        ENABLE_UNITTEST_FRIEND_ACCESS
      public:
        /** Constructor */
        inline ToHeapCache() { reserve(); }

        /** Move x onto the heap
         * \todo: Wrap return value in std::launder? I don't think it is needed
         */
        inline T *move_to_heap(T &&x) {
            // Construct our new T on pop()'s memory
            return new (pop()) T { std::move(x) }; // NOLINT
        }

        /** Reclaim the memory pointed to by non-null pointer x */
        inline void free(T *const x) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(x);
            x->~T(); // Invoke destructor
            data.emplace_back(x);
        }

        /** Save space by freeing extra cache items */
        inline void downsize() {
            Utils::Log::info("ToHeapCache: ", __func__, "Downsizing");
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
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(ToHeapCache, delete);

        /** Called if alloc fails */
        [[noreturn, gnu::cold]] void alloc_failed() noexcept {
            Utils::Log::critical("Allocation failed.");
            std::terminate(); // Crash the program
        }

        /** The allocation method */
        inline T *alloc() noexcept {
            void *const ret { std::malloc(sizeof(T)) }; // NOLINT
            if (ret != nullptr) {
                return static_cast<T *const>(ret);
            }
            alloc_failed();
        }

        /** Expand data to a size of at least dsize
         *  This will *not* shrink the data
         */
        inline void reserve() {
            if (data.size() >= dsize) {
                return;
            }
            data.reserve(dsize); // Can throw if max_length is exceeded
            const auto diff { dsize - data.size() };
            for (Constants::UInt i { 0 }; i < diff; ++i) {
                data.emplace_back(alloc());
            }
        }

        /** Pop an item from the cache for use */
        inline T *pop() {
            if (data.size() > 0) {
                const auto ret { data.back() };
                data.pop_back();
                return ret;
            }
            reserve();
            return alloc();
        }

        // Representation

        /** The size reserve will use */
        static const constexpr Constants::UInt dsize { 0x1000 };

        /** Internal data storage */
        std::vector<T *> data {};

        /** Error checking */
        static_assert(sizeof(Constants::UInt) == sizeof(typename decltype(data)::size_type),
                      "ToHeapCache size type assumptions are invalid.");
    };

} // namespace Utils

#endif
