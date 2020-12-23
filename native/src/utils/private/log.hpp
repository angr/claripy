/**
 * @file
   @brief This file defines the Utils::Private::log function
 */
#ifndef __UTILS_PRIVATE_LOG_HPP__
#define __UTILS_PRIVATE_LOG_HPP__

#include "log_level.hpp"

#include "../../constants.hpp"
#include "../sink.hpp" // todo


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used to designate certain items in utils as private
     *  These functions should not be called outside of the utils directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** Log the arguments given
         * @todo implement
         */
        template <typename... Args>
        void log(const Constants::Int id, const LogLevel lvl, Args &&...args) {
            ::Utils::sink(args...); // todo
            (void) lvl;
            (void) id;
        }

    } // namespace Private

} // namespace Utils

#endif
