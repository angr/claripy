/**
 * @file
 * \ingroup utils
 */
#include "recurrence_guard.hpp"

#include "affirm.hpp"
#include "error/unexpected.hpp"


// For brevity
using namespace Utils;


/** Static map to keep track of recurrences */
static thread_local std::map<std::string, Constants::UInt> count = {};


RecurrenceGuard::RecurrenceGuard(Constants::CCSC f, const Constants::UInt lim) : func(f) {
    const auto num = ++count[func];
    affirm<Error::Unexpected::RecurrenceLimit>(num <= lim, func,
                                               " has reached its recurrence limit of: ", lim);
}

RecurrenceGuard::~RecurrenceGuard() {
    auto &num = count[func];
    affirm<Error::Unexpected::Unknown>(
        num != 0, "RecurrenceGuard is trying to decrement a count of 0."
                  "\nThis probably happened because something went wrong with control flow."
                  "\nFor example, an exception was thrown in a guarded function but nothing was "
                  "cleaned up.");
    num -= 1;
}
