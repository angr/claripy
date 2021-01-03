/**
 * @file
 * \ingroup utils
 * @brief This file defines the cerr logging backend
 */
#ifndef __UTILS_LOG_BACKEND_CERR_HPP__
#define __UTILS_LOG_BACKEND_CERR_HPP__

#include "ostream.hpp"


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     *  When the buffer is flushed after each log call
     */
    struct Cerr : public OStream {

        /** Constructor */
        Cerr();
    };

} // namespace Utils::Log::Backend

#endif
