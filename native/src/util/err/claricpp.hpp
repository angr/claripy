/**
 * @file
 * \ingroup util
 * @brief This file contains the base claricpp exception
 * These exceptions have python analogs and must be caught and sent to python
 * via a different method.
 */
#ifndef R_UTIL_ERR_CLARICPP_HPP_
#define R_UTIL_ERR_CLARICPP_HPP_

#include "macros.hpp"

#include "../../constants.hpp"
#include "../fallback_error_log.hpp"
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

      public:
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

        /** Logs that an atomic was toggled */
        static void log_atomic_change(CCSC what, const bool old, const bool new_) noexcept;

        /** Warns that enabling backtraces causes a preformance hit */
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

        /** Get a previous backtrace; returns "" on error
         *  Get the a previous backtrace
         *  Ignores the last index'th backtraces
         *  Ex. index = 0 gets the last backtrace, index = 1 gets the second to last
         */
        static inline std::string backtrace(const std::size_t index = 0) noexcept {
            try {
                return backtraces.at(index).str(); // .at is memory safe
            }
            catch (...) {
                return {};
            }
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
        static thread_local std::deque<std::ostringstream> backtraces;

        /** The frame offset used when generating the backtrace
         *  This prevents Claricpp's internals from showing up in the backtrace
         *  This is found expirimentally; there is no issue if it is too small
         *  Being too small simply makes the backtraces messier as they contain this constructor
         */
        static const constexpr U64 frame_offset {
#ifdef __linux__
    #ifdef DEBUG
            5
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
