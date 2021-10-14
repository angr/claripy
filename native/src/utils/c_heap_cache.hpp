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

    /** A heap cache for objects of type In stored in C struct wrappers of type Wrap
     *  This is used to move stack objects onto the heap
     *  This assumes a Wrap's constructors work for In and In &&
     */
    template <typename In, typename Wrap> class CHeapCache {
        ENABLE_UNITTEST_FRIEND_ACCESS
        static_assert(!std::is_same_v<In, Wrap>, "In and Wrap should differ");

      public:
        /** Constructor */
        inline CHeapCache() { reserve(); }

        /** Move x onto the heap
         * \todo: Wrap return value in std::launder? I don't think it is needed
         */
        inline Wrap *move_to_heap(In &&x) {
            // Construct our new T on pop()'s memory
            return new (pop()) Wrap { std::forward<In>(x) }; // NOLINT
        }

        /** Construct an In in a Wrap on the heap */
        template <typename... Args> inline Wrap *emplace_on_heap(Args &&...args) {
            return move_to_heap(In { std::forward<Args>(args)... });
        }

        /** Reclaim the memory pointed to by non-null pointer x */
        inline void free(Wrap *const x) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(x);
            x->~Wrap(); // Invoke destructor
            data.emplace_back(x);
        }

        /** Save space by freeing extra cache items */
        inline void downsize() {
            Utils::Log::info("CHeapCache: ", __func__, "Downsizing");
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
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CHeapCache, delete);

        /** Called if alloc fails */
        [[noreturn, gnu::cold]] void alloc_failed() noexcept {
            Utils::Log::critical("Allocation failed.");
            std::terminate(); // Crash the program
        }

        /** The allocation method */
        inline Wrap *alloc() noexcept {
            void *const ret { std::malloc(sizeof(Wrap)) }; // NOLINT
            if (ret != nullptr) {
                return static_cast<Wrap *const>(ret);
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
        inline Wrap *pop() {
            if (data.size() > 0) {
                Wrap *const ret { data.back() };
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
        std::vector<Wrap *> data {};

        /** Error checking */
        static_assert(sizeof(Constants::UInt) == sizeof(typename decltype(data)::size_type),
                      "CHeapCache size type assumptions are invalid.");
    };

} // namespace Utils

#endif
