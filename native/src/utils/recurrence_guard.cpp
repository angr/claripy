/** @file */
#include "recurrence_guard.hpp"

thread_local std::map<std::string, Constants::UInt> Utils::RecurrenceGuard::count {};
