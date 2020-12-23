/**
 * @file
   @brief This file defines the Utils::DefaultLog
 */
#ifndef __UTILS_PRIVATE_DEFAULTLOG_HPP__
#define __UTILS_PRIVATE_DEFAULTLOG_HPP__

#include "../../macros.hpp"


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace used to designate certain items in utils as private
     *  These functions should not be called outside of the utils directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {

        /** DefaultLog is a class specifiying the log type is default */
        class DefaultLog {
            /** Disable construction */
            DELETE_DEFAULTS(DefaultLog)
            /** Disable Destruction */
            ~DefaultLog() = delete;
        };

    } // namespace Private

} // namespace Utils

#endif
