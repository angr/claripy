/**
 * @file
 @brief This file defines Utils::Log::Private::Default
 */
#ifndef __UTILS_PRIVATE_DEFAULT_HPP__
#define __UTILS_PRIVATE_DEFAULT_HPP__

#include "../../../macros.hpp"
#include "../macros.hpp"


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used for logging functions
     *  Unless otherwise specified, each function in this namespace takes in const reference
     *  arguments and returns void. There are no restrictions on what types of arguments,
     *  or how many arguments are given, other than that the '<<' stream operator must be defined
     *  for the type. Optionally, a class can be provided as an extra template argument to log. If
     *  it is provided the log written to will be a custom log related to that particular class.
     *  The Log class must have a static constexpr const char * const log_id definded.
     *  If no custom log is specified a default log is used.
     */
    namespace Log {

        /** A namespace used to designate certain items in Utils::Log as private
         *  These functions should not be called outside of Utils::Log members
         */
        namespace Private {

            /** DefaultLog is a class specifiying the log type is default */
            struct Default {
                UTILS_LOG_ENABLE_CUSTOM_LOGGING("Default")
              private:
                /** Disable construction */
                DELETE_DEFAULTS(Default)
                /** Disable Destruction */
                ~Default() = delete;
            };

        } // namespace Private

    } // namespace Log

} // namespace Utils

#endif
