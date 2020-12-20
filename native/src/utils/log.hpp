/**
 * @file
   @brief This file defines logging functions
 */
#ifndef __UTILS_LOG_HPP__
#define __UTILS_LOG_HPP__

#include "sink.hpp"


/** A namespace used for the utils directory */
namespace Utils {

    /** A function used to log anything with the << stream operator defined
     *  @todo create a logging system; probably via boost log? */
    template <typename... Args> void log(Args... args) {
#if DEBUG
        sink(args...); // todo
#else
        sink(args...);
#endif
    }

} // namespace Utils

#endif
