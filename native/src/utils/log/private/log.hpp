/**
 * @file
 * @brief This file defines a private logging which preps the arguments for the log backend
 */
#ifndef __UTILS_LOG_LOG_LOG_HPP__
#define __UTILS_LOG_LOG_LOG_HPP__

#include "../../../constants.hpp"
#include "../../apply.hpp"
#include "../../private/ostream.hpp"
#include "../../to_str.hpp"
#include "../level.hpp"
#include "../style/access.hpp"


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

            /** Prep the arguments then call the logging backend */
            template <typename... Args>
            void backend(Constants::CCSC id, const Level lvl, const Args &...args) {
                std::ostringstream s;
                apply<::Utils::Private::OStreamConst>(s, args...);
                const std::string msg = Style::get()(lvl, s);
                (void) msg;
                (void) id;
            }

        } // namespace Private

    } // namespace Log

} // namespace Utils

#endif
