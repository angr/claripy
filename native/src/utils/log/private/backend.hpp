/**
 * @file
 * @brief This file defines the Utils::Log::Private::backend function
 * @todo Maybe have a C++ backend and a python backend that hooks into python's logger?
 */
#ifndef __UTILS_LOG_PRIVATE_BACKEND_HPP__
#define __UTILS_LOG_PRIVATE_BACKEND_HPP__

#include "level.hpp"

#include "../../../constants.hpp"
#include "../../sink.hpp" // todo


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

            /** Log the arguments given
             * @todo implement
             */
            template <typename... Args>
            void backend(const char *const id, const Level lvl, const Args &...args) {
                ::Utils::sink(args...); // todo
                (void) lvl;
                (void) id;
            }

        } // namespace Private

    } // namespace Log

} // namespace Utils

#endif
