/**
 * @file
 * @brief This file defines the clog logging backend
 */
#ifndef __UTILS_LOG_BACKEND_CLOG_HPP__
#define __UTILS_LOG_BACKEND_CLOG_HPP__

#include "ostream.hpp"


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     */
    struct Clog : public OStream {

        /** Constructor */
        Clog();
    };

} // namespace Utils::Log::Backend

#endif
