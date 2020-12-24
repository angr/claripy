/**
 * @file
 @brief This file defines macros used acorss Utils::Log
 */
#ifndef __UTILS_LOG_MACROS_HPP__
#define __UTILS_LOG_MACROS_HPP__


/** A macro used to give a class a custom log (instead of using the default log)
 *  This must be placed in the 'public' section of the class
 */
#define UTILS_LOG_ENABLE_CUSTOM_LOGGING(NAME)                                                     \
    /** Create a custom log for this class */                                                     \
    static constexpr auto log_id = NAME;


#endif
