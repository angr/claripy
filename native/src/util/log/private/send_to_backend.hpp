/**
 * @file
 * \ingroup util
 * @brief This file defines a function which preps its args then sends them to the Log Backend
 */
#ifndef R_UTIL_LOG_PRIVATE_SENDTOBACKEND_HPP_
#define R_UTIL_LOG_PRIVATE_SENDTOBACKEND_HPP_

#include "../../ostream.hpp"
#include "../backend.hpp"
#include "../style.hpp"

#include <sstream>


namespace Util::Log::Private {

    /** Prep the arguments then call the logging backend */
    template <typename... Args>
    inline void send_to_backend(CCSC id, const Level::Level lvl, Args &&...args) {
        UTIL_ASSERT_NOT_NULL_DEBUG(Style::get());   // Sanity check
        UTIL_ASSERT_NOT_NULL_DEBUG(Backend::get()); // Sanity check
        std::ostringstream s;
        (OStream(s, std::forward<Args>(args)), ...);
        const std::string msg { Style::get()->str(id, lvl, s) };
        Backend::get()->log(id, lvl, msg);
    }

} // namespace Util::Log::Private

#endif
