/**
 * @file
 * \ingroup util
 * @brief This file contains the base claricpp exception
 * These exceptions have python analogs and must be caught and sent to python
 * via a different method.
 */
#ifndef R_UTIL_ERR_CLARICPP_HPP_
#define R_UTIL_ERR_CLARICPP_HPP_

#include "../../constants.hpp"
#include "../../macros.hpp"
#include "../to_str.hpp"

#include <atomic>
#include <exception>
#include <string>


namespace Util::Err {

    /** The base claricpp exception class
     *  Any exception thrown intentionally must subclass this
     *  Note: Since exceptions do not need to be super fast and since we have const date members:
     *  for clarity we ignore the rule of 5 in favor of what the compiler defaults. Subclasses
     *  of Claricpp should feel free to do the same unless they have non-const data members
     */
    class Claricpp : public std::exception {
        /** Allow all error factories friend access */
        template <typename T, typename S> friend T factory(const S msg);

      public:
        /** Constructor: This constructor consumes its arguments via const reference */
        template <typename... Args>
        explicit Claricpp(Args &&...args)
            : msg(Util::to_str(std::forward<Args>(args)...)), bt { save_backtrace() } {}

        /** Default virtual destructor */
        ~Claricpp() noexcept override = default;

        // Rule of 5
        SET_IMPLICITS_NONDEFAULT_CTORS(Claricpp, delete);

        inline std::string backtrace() const noexcept { return bt.str(); }

        /** Enable / disable backtraces
         *  Returns the old state
         */
        static inline bool toggle_backtrace(bool set) noexcept {
            return enable_backtraces.exchange(set);
        }

        /** Return true if and only if backtraces are enabled */
        static inline bool backtraces_enabled() noexcept { return enable_backtraces; }

        /** Enable / disable appending backtraces
         *  Returns the old state
         */
        static inline bool toggle_append_backtrace(bool set) noexcept {
            return append_backtrace.exchange(set);
        }

        /** Return true if and only if backtraces are enabled */
        static inline bool append_backtraces_enabled() noexcept { return append_backtrace; }

        /** Message getter
         *  If enable_backtraces and append_backtraces, appends a backtrace
         */
        [[nodiscard]] inline const char *raw_what() const noexcept { return msg.c_str(); }

        /** Message getter
         *  If enable_backtraces and append_backtraces, appends a backtrace
         *  Warning: Will return dynamically allocated memory if a backtrace is included
         *  Note: If something goes wrong trying to print the backtrace, skips it
         */
        [[nodiscard]] inline const char *what() const noexcept override final {
            if (enable_backtraces && append_backtrace) {
                try {
                    auto out { backtrace() };
                    out + "\n\n" + msg;
                    char *const ret { static_cast<char *const>(std::malloc(out.size() + 1)) };
                    if (ret != nullptr) {
                        std::strcpy(ret, out.c_str());
                        return ret;
                    }
                }
                catch (std::exception &) {
                }
            }
            return raw_what();
        }

      private:
        /** Saves a backtrace */
        static std::ostringstream save_backtrace() noexcept;

        // Representation

        /** The message */
        const std::string msg;
        /** The backtrace */
        const std::ostringstream bt;

        // Statics

        /** True if backtraces should be enabled */
        static std::atomic_bool enable_backtraces;
        /** If true and if enable_backtraces, what() will contain a backtrace */
        static std::atomic_bool append_backtrace;
        /** The frame offset used when generating the backtrace
         *  This prevents Claricpp's internals from showing up in the backtrace
         *  This is found expirimentally; there is no issue if it is too small
         *  Being too small simply makes the backtraces messier as they contain this constructor
         */
        static const constexpr UInt frame_offset {
#if defined(__APPLE__) || defined(__MACH__)
            3
#else
            2
#endif
        }; // NOLINT
    };

} // namespace Util::Err

#endif
