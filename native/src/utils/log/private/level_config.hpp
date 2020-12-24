/**
 * @file
 * @brief This file defines which log levels are enabled
 */
#ifndef __UTILS_LOG_PRIVATE_LEVELCONFIG_HPP__
#define __UTILS_LOG_PRIVATE_LEVELCONFIG_HPP__


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used for logging functions
     *  Unless otherwise specified, each public logging function in this namespace takes in
     * whatever arguments it is given by copy, and returns void. There are no restrictions on what
     * types of arguments, or how many arguments are given, other than that the '<<' stream
     * operator must be defined for the type. Optionally, a class can be provided as an extra
     * template argument to log. If it is provided the log written to will be a custom log related
     * to that particular class. If no custom log is specified a default log is used.
     */
    namespace Log {

        /** A namespace used to designate certain items in Utils::Log as private
         *  These functions should not be called outside of Utils::Log members
         */
        namespace Private {

            /** A namespace used to hold boolean which determine which logs are enabled */
            namespace Enabled {

                /** Enable / disable verbose log level */
                constexpr const bool verbose =
#ifdef VERBOSE_LOG
                    true;
#else
                    false;
#endif

                /** Enable / disable debug log level */
                constexpr const bool debug =
#ifdef DEBUG_LOG
                    true;
#else
                    false;
#endif

                /** Enable / disable info log level */
                constexpr const bool info =
#ifdef INFO_LOG
                    true;
#else
                    false;
#endif

                /** Enable / disable warning log level */
                constexpr const bool warning =
#ifdef WARNING_LOG
                    true;
#else
                    false;
#endif

                /** Enable / disable error log level */
                constexpr const bool error =
#ifdef ERROR_LOG
                    true;
#else
                    false;
#endif

                /** Enable / disable critical log level */
                constexpr const bool critical =
#ifdef CRITICAL_LOG
                    true;
#else
                    false;
#endif

            } // namespace Enabled

        } // namespace Private

    } // namespace Log

} // namespace Utils

#endif
