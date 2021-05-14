/**
 * @file
 * \ingroup utils
 * @brief This file defines the clog logging backend
 */
#ifndef R_UTILS_LOG_BACKEND_CLOG_HPP_
#define R_UTILS_LOG_BACKEND_CLOG_HPP_

#include "ostream.hpp"

#include <iostream>


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     *  When the buffer is flushed is deffered to std::clog
     */
    struct Clog final : public OStream {

        /** Constructor */
        inline Clog() : OStream(std::make_shared<std::ostream>(std::clog.rdbuf()), false, false) {}
    };

} // namespace Utils::Log::Backend

#endif
