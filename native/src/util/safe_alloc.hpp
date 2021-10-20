/**
 * @file
 * \ingroup util
 * @brief This file defines safe allocation functions
 */
#ifndef R_UTIL_SAFEALLOC_HPP_
#define R_UTIL_SAFEALLOC_HPP_

#include "affirm.hpp"
#include "log.hpp"

#include <cstdlib>
#include <new>


namespace Util::Safe {

    /** Called if a safe method fails */
    [[noreturn, gnu::cold]] inline void terminate(CCSC msg) noexcept {
        Log::critical(msg);
        std::terminate();
    };

    /** Malloc, but raises an exception if the allocation fails */
    template <typename T> T *malloc(const std::size_t count) {
        T *const ret { static_cast<T *const>(std::malloc(count * sizeof(T))) }; // NOLINT
        Util::affirm<std::bad_alloc>(ret != nullptr);
        return ret;
    }

} // namespace Util::Safe

#endif
