/**
 * @file
 * \ingroup utils
 * @brief This file defines a thread-safe abstract class
 * Thread-Safe wrapper classes should derive from this
 * That is, if a class' purpose is to enforce thread safety upon some
 * owned object, it should derive from this class
 */
#ifndef R_UTILS_THREADSAFE_BASE_HPP_
#define R_UTILS_THREADSAFE_BASE_HPP_

#include "../../macros.hpp"


namespace Utils::ThreadSafe {

    /** A thread-safe abstract class
     * Thread-Safe wrapper classes should derive from this
     * That is, if a class' purpose is to enforce thread safety upon some object,
     * it should derive from this class
     * Locks, for example, should *not* derive from this class; they do not inherently
     * own what they guard, they are just a guard mechanism.
     * Something like std::atomic should derive from this
     */
    struct Base {
        /** Virtual destructor */
        virtual ~Base() noexcept = default;
        // Rule of 5
        SET_IMPLICITS(Base, default);
    };

} // namespace Utils::ThreadSafe

#endif
