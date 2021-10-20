/**
 * @file
 * \ingroup util
 * @brief This file defines safe allocation functions
 */
#ifndef R_UTIL_SAFEALLOC_HPP_
#define R_UTIL_SAFEALLOC_HPP_

#include "affirm.hpp"

#include <cstdlib>
#include <new>

namespace Util::Safe {

    /** Malloc, but raises an exception if the allocation fails */
    template <typename T> T *malloc(const std::size_t count) {
        T *const ret { static_cast<T *>(std::malloc(count * sizeof(T))) }; // NOLINT
        Util::affirm<std::bad_alloc>(ret != nullptr);
        return ret;
    }

} // namespace Util::Safe

#endif
