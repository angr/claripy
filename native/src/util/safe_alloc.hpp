/**
 * @file
 * \ingroup util
 * @brief This file defines safe allocation functions
 */
#ifndef R_SRC_UTIL_SAFEALLOC_HPP_
#define R_SRC_UTIL_SAFEALLOC_HPP_

#include "assert.hpp"
#include "log.hpp"

#include <cstdlib>
#include <new>


namespace Util::Safe {

    /** Malloc, but raises an exception if the allocation fails
     *  Consider using new[N] if possible
     */
    template <typename T> T *malloc(const std::size_t count) {
        static_assert(!std::is_same_v<T, char>, "Use new[]");
        T *const ret { static_cast<T *const>(std::malloc(count * sizeof(T))) }; // NOLINT
        if (UNLIKELY(!ret)) {
            throw std::bad_alloc();
        }
        return ret;
    }

} // namespace Util::Safe

#endif
