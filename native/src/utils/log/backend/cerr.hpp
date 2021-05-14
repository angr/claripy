/**
 * @file
 * \ingroup utils
 * @brief This file defines the cerr logging backend
 */
#ifndef R_UTILS_LOG_BACKEND_CERR_HPP_
#define R_UTILS_LOG_BACKEND_CERR_HPP_

#include "ostream.hpp"

#include <iostream>


namespace Utils::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     *  When the buffer is flushed after each log call
     */
    struct Cerr final : public OStream {

        /** Constructor */
        inline Cerr() : OStream(std::make_shared<std::ostream>(std::cerr.rdbuf()), true, false) {}
    };

} // namespace Utils::Log::Backend

#endif
