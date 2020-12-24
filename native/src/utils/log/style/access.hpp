/**
 * @file
 * @brief This file methods for accessing the log style
 */
#ifndef __UTILS_LOG_STYLE_ACCESS_HPP__
#define __UTILS_LOG_STYLE_ACCESS_HPP__

#include "abstract_base.hpp"


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

        /** A namespace used for log styles */
        namespace Style {

            /** Set the logging style by copy */
            void set(AbstractBase s);

            /** Return a copy of the style */
            AbstractBase get();

        } // namespace Style

    } // namespace Log

} // namespace Utils

#endif
