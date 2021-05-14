/**
 * @file
 * \ingroup utils
 * @brief This file provides an thread-safe atomic class
 */
#ifndef R_UTILS_THREADSAFE_ATOMIC_HPP_
#define R_UTILS_THREADSAFE_ATOMIC_HPP_

#include "base.hpp"

#include <atomic>


namespace Utils::ThreadSafe {

    /** A thread-safe atomic that derives from Base */
    template <typename T> struct Atomic final : public Base {
        /** We simple expose an std::atomic */
        std::atomic<T> atomic;
    };

} // namespace Utils::ThreadSafe

#endif
