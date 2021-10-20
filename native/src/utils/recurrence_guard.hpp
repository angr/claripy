/**
 * @file
 * \ingroup utils
 * @brief This file defines a thread-safe recurrence guard
 */
#ifndef R_UTILS_RECURRENCEGUARD_HPP_
#define R_UTILS_RECURRENCEGUARD_HPP_

#include "affirm.hpp"
#include "error/unexpected.hpp"

#include "../constants.hpp"
#include "../macros.hpp"

#include <map>
#include <string>


/** A macro to make creating a recurrence guard easier */
#define UTILS_RECURRENCE_GUARD ::Utils::RecurrenceGuard __recurrence_guard(__func__);

/** A macro to make creating a recurrence guard with a custom limit easier */
#define UTILS_RECURRENCE_GUARD_LIM(LIM)                                                           \
    ::Utils::RecurrenceGuard __recurrence_guard(__func__, (LIM));


namespace Utils {

    /** A thread-safe recurrence guard class
     *  Warning: The destructor of the recurrence guard may throw!
     *  Note: The destructor will not throw if std::uncaught_exceptions differs
     *  from the value it had during the initial construction of RecurrenceGuard
     *  Note that a recurrence in another thread, even if created by this thread, will not count
     */
    class RecurrenceGuard final {
      public:
        /** Constructor
         *  Takes in optional recurrence limit argument
         *  Default argument value: 1000
         */
        explicit inline RecurrenceGuard(CCSC f, const UInt lim = 1000)
            : func(f)
#ifdef DEBUG
              ,
              n_except(std::uncaught_exceptions())
#endif
        {
            const auto num { ++count[func] };
            affirm<Error::Unexpected::RecurrenceLimit>(
                num <= lim, WHOAMI_WITH_SOURCE, func,
                " has reached its recurrence limit of: ", lim);
        }

        /** Destructor
         *  Warning: This destructor may throw when DEBUG mode is enabled
         */
        inline ~RecurrenceGuard()
#ifdef DEBUG
            noexcept(false) {
            auto &num { count[func] };
            // Check for stack unwinding
            if (n_except == std::uncaught_exceptions()) {
                // Error checking
                affirm<Error::Unexpected::Unknown>(
                    num != 0, WHOAMI_WITH_SOURCE
                    "RecurrenceGuard is trying to decrement a count of 0."
                    "\nThis probably happened because something went wrong with control flow."
                    "\nFor example, an exception was thrown in a guarded function but nothing was "
                    "cleaned up.");
            }
            num -= 1;
        }
#else
        {
            count[func] -= 1;
        }
#endif

      private:
        /** The name of the function */
        const std::string func;

#ifdef DEBUG
        /** The number of uncaught exceptions alive during construction */
        const int n_except;
#endif

        /** Static map to keep track of recurrences */
        static thread_local std::map<std::string, UInt> count;

        // Disable other creation methods
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RecurrenceGuard, delete)
    };

} // namespace Utils

#endif
