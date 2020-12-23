/**
 * @file
   @brief This file defines the Utils::Private::LogLevel typesafe enum
 */
#ifndef __UTILS_PRIVATE_LOGLEVEL_HPP__
#define __UTILS_PRIVATE_LOGLEVEL_HPP__


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used to designate certain items in utils as private
     *  These functions should not be called outside of the utils directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** A typesafe enum denoting different log levels */
        enum class LogLevel { Status, Debug, Verbose, Warning, Error };

    } // namespace Private

} // namespace Utils

#endif
