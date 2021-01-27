/**
 * @file
 * \ingroup utils
 * @brief This file defines a thread-safe recurence guard
 */
#ifndef __UTILS_RECURRENCEGUARD_HPP__
#define __UTILS_RECURRENCEGUARD_HPP__

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
     *  Note that a recurrence in another thread, even if created by this thread, will not count
     */
    class RecurrenceGuard {
      public:
        /** Constructor
         *  Takes in optional recurrence limit argument
         *  Default argument value: 1000
         */
        explicit RecurrenceGuard(Constants::CCSC f, const Constants::UInt lim = 1000);

        /** Destructor */
        ~RecurrenceGuard();

      private:
        /** The name of the function */
        const std::string func;

        // Disable other creation methods
        SET_IMPLICITS_EXCLUDE_DEFAULT_CONSTRUCTOR(RecurrenceGuard, delete)
    };

} // namespace Utils

#endif
