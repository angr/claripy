/** @file */
#include "runtime_level_config.hpp"

#ifdef RUNTIME_LOGLEVEL

// For brevity
namespace E = Utils::Log::Private::Enabled;

bool E::verbose =
    #ifdef VERBOSE_LOG
    true;
    #else
    false;
    #endif

bool E::debug =
    #ifdef DEBUG_LOG
    true;
    #else
    false;
    #endif

bool E::info =
    #ifdef INFO_LOG
    true;
    #else
    false;
    #endif

bool E::warning =
    #ifdef WARNING_LOG
    true;
    #else
    false;
    #endif

bool E::error =
    #ifdef ERROR_LOG
    true;
    #else
    false;
    #endif

bool E::critical =
    #ifdef CRITICAL_LOG
    true;
    #else
    false;
    #endif

#endif
