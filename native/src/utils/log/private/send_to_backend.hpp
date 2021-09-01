/**
 * @file
 * \ingroup utils
 * @brief This file defines a function which preps its args then sends them to the Log Backend
 */
#ifndef R_UTILS_LOG_PRIVATE_SENDTOBACKEND_HPP_
#define R_UTILS_LOG_PRIVATE_SENDTOBACKEND_HPP_

#include "../../ostream.hpp"
#include "../backend.hpp"
#include "../style.hpp"

#include <sstream>


namespace Utils::Log::Private {

    /** Prep the arguments then call the logging backend */
    template <typename... Args>
    inline void send_to_backend(Constants::CCSC id, const Level::Level lvl, Args &&...args) {
        UTILS_AFFIRM_NOT_NULL_DEBUG(Style::get());   // Sanity check
        UTILS_AFFIRM_NOT_NULL_DEBUG(Backend::get()); // Sanity check
        std::ostringstream s;
        (OStream(s, std::forward<Args>(args)), ...);
        const std::string msg { Style::get()->str(id, lvl, s) };
        Backend::get()->log(id, lvl, msg);
    }

} // namespace Utils::Log::Private

#endif
