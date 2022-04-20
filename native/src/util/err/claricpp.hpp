/**
 * @file
 * \ingroup util
 * @brief This file contains the base claricpp exception
 * These exceptions have python analogs and must be caught and sent to python
 * via a different method.
 */
#ifndef R_SRC_UTIL_ERR_CLARICPP_HPP_
#define R_SRC_UTIL_ERR_CLARICPP_HPP_

#include "macros.hpp"

#include "../../constants.hpp"
#include "../backtrace.hpp"
#include "../fallback_error_log.hpp"
#include "../terminate.hpp"
#include "../to_str.hpp"

#include <atomic>
#include <cstring>
#include <deque>
#include <exception>
#include <string>


namespace Util::Err {

    /** The base claricpp exception class
     *  Any exception thrown intentionally must subclass this
     *  Note: Since exceptions do not need to be super fast and since we have const date members:
     *  for clarity we ignore the rule of 5 in favor of what the compiler defaults. Subclasses
     *  of Claricpp should feel free to do the same unless they have non-const data members
     *  This class saves the last n_backtraces backtraces
     */
    class Claricpp : public std::exception {
        /** Allow all error factories friend access */
        template <typename T, typename S> friend T factory(const S msg);
        /** Backtrace generator function */
        static inline constexpr auto &generator { ::Util::Backtrace::backward };

      public:
        /** Backtrace holder type */
        using LazyTrace = ::Util::Backtrace::Lazy;

        // Rule of 5

        /** Constructor: This constructor consumes its arguments via const reference */
        explicit inline Claricpp(std::string &&msg_) : msg { std::move(msg_) } {
            if (backtraces_enabled()) {
                save_backtrace();
            }
        }

        /** Default virtual destructor */
        ~Claricpp() noexcept override = default;

        // Rule of 5
        SET_IMPLICITS_NONDEFAULT_CTORS(Claricpp, delete);

        // Functions

        /** Logs that an atomic was toggled */
        static void log_atomic_change(CCSC what, const bool old, const bool new_) noexcept;

        /** Warns that enabling backtraces causes a performance hit */
        static void warn_backtrace_slow() noexcept;

        /** Enable / disable backtraces
         *  Returns the old state
         */
        static inline bool toggle_backtrace(const bool set, const bool log_me = false) noexcept {
            const bool ret { enable_backtraces.exchange(set) };
            if (UNLIKELY((log_me))) {
                log_atomic_change("Claricpp backtrace functionality", ret, set);
            }
            if (set) {
                warn_backtrace_slow();
            }
            return ret;
        }

        /** Return true if and only if backtraces are enabled */
        static inline bool backtraces_enabled() noexcept { return enable_backtraces; }

        /** Message getter */
        [[nodiscard]] inline const char *what() const noexcept final { return msg.c_str(); }

        /** Get a previous backtrace in an unevaluated form; returns {} on error
         *  Get the a previous backtrace
         *  Ignores the last index'th backtraces
         *  Ex. index = 0 gets the last backtrace, index = 1 gets the second to last
         *  Call ->str() on the result to get the backtrace as a string
         */
        static inline LazyTrace::Ptr lazy_backtrace(const std::size_t index = 0) noexcept {
            if (backtraces_enabled()) {
                try {
                    // shared_ptrs can safely be copy constructed between threads
                    if (LIKELY(index < backtraces.size())) {
                        return backtraces[index];
                    }
                    UTIL_NEW_FALLBACK_ERROR_LOG("Index out of range: ", index);
                }
                UTIL_FALLBACKLOG_CATCH("Failed to get backtrace ", index)
            }
            // No trace to return
            return {};
        }

        /** Eagerly evaluated lazy_backtrace(index)
         *  If lazy_backtrace(index) returns nullptr; will return {}
         *  Unlike lazy_backtrace, this may throw if evaluation fails
         */
        static inline std::string backtrace(const std::size_t index = 0) {
            const auto ptr { lazy_backtrace(index) };
            if (ptr == nullptr) {
                return {};
            }
            return ptr->str();
        }

      private:
        /** Generate and save a backtrace */
        void save_backtrace() noexcept;

        /** The message */
        const std::string msg;

        /** True if backtraces should be enabled */
        static std::atomic_bool enable_backtraces;
        /** The number of previous backtraces Claricpp will store */
        static const constexpr U64 n_backtraces { 3_ui };
        /** The last saved backtraces; newest come first */
        static thread_local std::deque<LazyTrace::Ptr> backtraces;

        /** The frame offset used when generating the backtrace
         *  This prevents Claricpp's internals from showing up in the backtrace
         *  This is found experimentally; there is no issue if it is too small
         *  Being too small simply makes the backtraces messier as they contain this constructor
         */
        static const constexpr uint16_t frame_offset {
#ifdef __linux__
    #ifdef DEBUG
            4
    #else
            3
    #endif
#elif defined(__APPLE__) || defined(__MACH__)
            3
#else
            2
#endif
        }; // NOLINT
    };

} // namespace Util::Err

#endif
