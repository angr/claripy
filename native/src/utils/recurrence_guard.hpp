/**
 * @file
 * \ingroup utils
 * @brief This file defines a thread-safe recurence guard
 */
#ifndef __UTILS_RECURRENCEGUARD_HPP__
#define __UTILS_RECURRENCEGUARD_HPP__

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
     *  Note that a recurrence in another thread, even if created by this thread, will not count
     */
    class RecurrenceGuard {
      public:
        /** Constructor
         *  Takes in optional recurrence limit argument
         *  Default argument value: 1000
         */
        explicit inline RecurrenceGuard(Constants::CCSC f, const Constants::UInt lim = 1000)
            : func(f) {
            const auto num { ++count[func] };
            affirm<Error::Unexpected::RecurrenceLimit>(
                num <= lim, func, " has reached its recurrence limit of: ", lim);
        }

        /** Destructor
         *  Warning: This destructor may throw!
         */
        inline ~RecurrenceGuard() {
            auto &num = count[func];
            affirm<Error::Unexpected::Unknown>(
                num-- != 0,
                "RecurrenceGuard is trying to decrement a count of 0."
                "\nThis probably happened because something went wrong with control flow."
                "\nFor example, an exception was thrown in a guarded function but nothing was "
                "cleaned up.");
        }

      private:
        /** The name of the function */
        const std::string func;

        /** Static map to keep track of recurrences */
        inline static thread_local std::map<std::string, Constants::UInt> count {};

        // Disable other creation methods
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(RecurrenceGuard, delete)
    };

} // namespace Utils

#endif
