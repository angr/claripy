/**
 * @file
 * \ingroup util
 * @brief This file defines a thread-safe recurrence guard
 */
#ifndef R_SRC_UTIL_RECURRENCEGUARD_HPP_
#define R_SRC_UTIL_RECURRENCEGUARD_HPP_

#include "assert.hpp"
#include "err.hpp"
#include "fallback_error_log.hpp"

#include "../constants.hpp"
#include "../macros.hpp"

#include <map>
#include <string>


/** A macro to make creating a recurrence guard easier */
#define UTIL_RECURRENCE_GUARD ::Util::RecurrenceGuard __recurrence_guard(__func__);

/** A macro to make creating a recurrence guard with a custom limit easier */
#define UTIL_RECURRENCE_GUARD_LIM(LIM) ::Util::RecurrenceGuard __recurrence_guard(__func__, (LIM));


namespace Util {

    /** A thread-safe recurrence guard class
     *  Note that a recurrence in another thread, even if created by this thread, will not count
     */
    class RecurrenceGuard final {
      public:
        /** Constructor
         *  Takes in optional recurrence limit argument
         *  Default argument value: 1000
         */
        explicit inline RecurrenceGuard(CCSC f, const U64 lim = 1000) : func(f) {
            const auto num { ++count[func] };
            UTIL_ASSERT(Err::RecurrenceLimit, num <= lim, func,
                        " has reached its recurrence limit of: ", lim);
        }

        /** Destructor */
        inline ~RecurrenceGuard() noexcept {
            auto &num { count[func] };
#ifdef DEBUG
            // Check for stack unwinding
            if (UNLIKELY(num == 0)) {
                UTIL_NEW_FALLBACK_ERROR_LOG(
                    "\nThis probably happened because something went wrong with control flow."
                    "\nFor example, an exception was thrown in a guarded function but nothing was "
                    "cleaned up.");
            }
#endif
            num -= 1;
        }

      private:
        /** The name of the function */
        const std::string func;

        /** Static map to keep track of recurrences */
        static thread_local std::map<std::string, U64> count;

        // Disable other creation methods
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RecurrenceGuard, delete)
    };

} // namespace Util

#endif
