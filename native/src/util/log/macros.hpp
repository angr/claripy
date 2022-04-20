/**
 * @file
 * \ingroup util
 * @brief This file defines macros used across Util::Log
 */
#ifndef R_SRC_UTIL_LOG_MACROS_HPP_
#define R_SRC_UTIL_LOG_MACROS_HPP_

#include "constants.hpp"

#include "../type.hpp"


/** A macro used to give a class a custom log (instead of using the default log)
 *  This must be placed in the 'public' section of the class
 */
#define UTIL_LOG_ENABLE_CUSTOM_LOGGING(NAME)                                                       \
    /** Create a custom log for this class */                                                      \
    static const constexpr Util::Log::LogID log_id { (NAME) };

/** Define a custom logging class
 *  This class can be passed to a log function as a template parameter to log to a custom log
 *  rather than the default log.
 */
#define UTIL_LOG_DEFINE_LOG_CLASS(NAME)                                                            \
    /** Define a custom logging class */                                                           \
    struct NAME final : private ::Util::Type::Unconstructable {                                    \
        UTIL_LOG_ENABLE_CUSTOM_LOGGING(#NAME)                                                      \
    };


#endif
