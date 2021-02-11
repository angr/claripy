/**
 * @file
 * \ingroup utils
 * @brief This file defines a thread-safe abstract class
 * Thread-Safe wrapper classes should derive from this
 * That is, if a class' purpose is to enforce thread safety upon some
 * owned object, it should derive from this class
 */
#ifndef __UTILS_THREADSAFE_BASE_HPP__
#define __UTILS_THREADSAFE_BASE_HPP__


namespace Utils::ThreadSafe {

    /** A thread-safe abstract class
     * Thread-Safe wrapper classes should derive from this
     * That is, if a class' purpose is to enforce thread safety upon some object,
     * it should derive from this class
     * Locks, for example, should *not* derive from this class; they do not inherently
     * own what they guard, they are just a guard mechanism.
     * Something like std::atomic should derive from this
     */
    class Base {};

} // namespace Utils::ThreadSafe

#endif
