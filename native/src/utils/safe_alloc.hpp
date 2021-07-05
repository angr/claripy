/**
 * @file
 * \ingroup utils
 * @brief This file defines safe allocation functions
 */
#ifndef R_UTILS_SAFEALLOC_HPP_
#define R_UTILS_SAFEALLOC_HPP_

#include "affirm.hpp"

#include <cstdlib>
#include <new>

namespace Utils::Safe {

    /** Malloc, but raises an exception if the allocation fails */
    template <typename T> T *malloc(const std::size_t count) {
        T *const ret { static_cast<T *>(std::malloc(count * sizeof(T))) }; // NOLINT
        Utils::affirm<std::bad_alloc>(ret != nullptr);
        return ret;
    }

} // namespace Utils::Safe

#endif
