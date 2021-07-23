/**
 * @file
 * \ingroup utils
 * @brief This file contains the base claricpp exception
 * These exceptions have python analogs and must be caught and sent to python
 * via a different method.
 */
#ifndef R_UTILS_ERROR_CLARICPP_HPP_
#define R_UTILS_ERROR_CLARICPP_HPP_

#include "../../macros.hpp"
#include "../to_str.hpp"

#include <atomic>
#include <exception>
#include <string>

namespace Utils::Error {

#ifdef DEBUG
    namespace Private {
        /** A function that prints the backtrace if in debug mode, else is a no-op */
        void backtrace_if_debug();
    }; // namespace Private
#endif

    /** The base claricpp exception class
     *  Any exception thrown intentionally must subclass this
     *  Note: Since exceptions do not need to be super fast and since we have const date members:
     *  for clarity we ignore the rule of 5 in favor of what the compiler defaults. Subclasses
     *  of Claricpp should feel free to do the same unless they have non-const data members
     */
    class Claricpp : public std::exception {
      public:
        /** Constructor: This constructor consumes its arguments via const reference */
        template <typename... Args>
        explicit Claricpp(const Args &...args) : msg(Utils::to_str(args...)) {
#ifdef DEBUG
            Private::backtrace_if_debug();
#endif
        }

#ifdef DEBUG
        /** Enable / disable backtraces
         *  Returns the old state
         */
        static inline bool toggle_backtrace(bool set) noexcept {
            enable_backtraces.exchange(set, std::memory_order::memory_order_relaxed);
            return set;
        }

        /** Return true if and only if backtraces are enabled */
        static inline bool backtraces_enabled() noexcept { return enable_backtraces; }
#endif

        // Rule of 5 (note that std::string is not noexcept constructible)
        SET_IMPLICITS_CONST_MEMBERS(Claricpp, default, noexcept);

        /** Default virtual destructor */
        ~Claricpp() noexcept override = default;

        /** Message getter */
        [[nodiscard]] inline const char *what() const noexcept override final {
            return msg.c_str();
        }

      private:
        /** The message */
        const std::string msg;

#ifdef DEBUG
        /** True if backtraces should be enabled */
        static thread_local std::atomic_bool enable_backtraces;
#endif

        /** Allow all error factories friend access */
        template <typename T, typename S> friend T factory(const S msg);
    };

} // namespace Utils::Error

#endif
