/**
 * @file
   @brief This file defines logging functions
 */
#ifndef __UTILS_LOG_HPP__
#define __UTILS_LOG_HPP__


/** A namespace used for the utils directory */
namespace Utils {

    /** A function used to log anything with the << stream operator defined */
    template <typename... Args> void log(Args... args) {
#if DEBUG

#endif
    }

} // namespace Utils

#endif
