/**
 * @file
 @brief This file defines a function that returns a unique id for each class
 */
#ifndef __UTILS_LOG_PRIVATE_ID_HPP__
#define __UTILS_LOG_PRIVATE_ID_HPP__

#include "../../../macros.hpp"
#include "../../inc.hpp"


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

            /** Assign a different value to each log type */
            template <typename T> Constants::Int ID() {
                const static Constants::Int id = inc<T>();
                return id;
            }

        } // namespace Private

    } // namespace Log

} // namespace Utils

#endif
