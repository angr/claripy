/**
 * @file
 * @brief This file defines the default log style
 */
#ifndef __UTILS_LOG_STYLE_DEFAULT_HPP__
#define __UTILS_LOG_STYLE_DEFAULT_HPP__

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

            /** The default log style class */
            struct Default : public AbstractBase {
                /** Format the log message */
                std::string operator()(const Level &lvl,
                                       std::ostringstream &raw) const override final;
            };

        } // namespace Style

    } // namespace Log

} // namespace Utils

#endif
