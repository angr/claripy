/**
 * @file
 @brief This file defines macros used acorss Utils::Log
 */
#ifndef __UTILS_LOG_MACROS_HPP__
#define __UTILS_LOG_MACROS_HPP__

#include "../unconstructable.hpp"


/** Define a custom logging class
 *  This class can be passed to a log function as a template parameter to log to a custom log
 *  rather than the default log.
 */
#define UTILS_LOG_DEFINE_LOG_CLASS(NAME)                                                          \
    /** Define a custom logging class */                                                          \
    struct NAME : private ::Utils::Unconstructable {                                              \
        static constexpr auto log_id = #NAME;                                                     \
    };

/** A macro used to give a class a custom log (instead of using the default log)
 *  This must be placed in the 'public' section of the class
 */
#define UTILS_LOG_ENABLE_CUSTOM_LOGGING(NAME)                                                     \
    /** Create a custom log for this class */                                                     \
    static constexpr auto log_id = NAME;


#endif
