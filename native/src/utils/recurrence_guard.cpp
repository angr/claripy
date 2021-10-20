/** @file */
#include "recurrence_guard.hpp"

thread_local std::map<std::string, UInt> Utils::RecurrenceGuard::count {};
