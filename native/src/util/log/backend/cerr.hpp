/**
 * @file
 * \ingroup util
 * @brief This file defines the cerr logging backend
 */
#ifndef R_SRC_UTIL_LOG_BACKEND_CERR_HPP_
#define R_SRC_UTIL_LOG_BACKEND_CERR_HPP_

#include "ostream.hpp"

#include <iostream>


namespace Util::Log::Backend {

    /** The stream backend
     *  This takes in an ostream and logs to it
     *  When the buffer is flushed after each log call
     */
    struct Cerr final : public OStream {
        /** Backend name */
        inline const char *name() const noexcept final { return "Cerr"; }
        /** Constructor */
        inline Cerr() : OStream(std::make_shared<std::ostream>(std::cerr.rdbuf()), true, false) {}
    };

} // namespace Util::Log::Backend

#endif
