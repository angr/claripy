/**
 * @file
 * \ingroup util
 */
#include "recurrence_guard.hpp"

thread_local std::map<std::string, U64> Util::RecurrenceGuard::count {};
