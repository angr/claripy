/**
 * @file
 * \ingroup utils
 * @brief This file defines a function which preps its args then sends them to the Log Backend
 */
#ifndef __UTILS_LOG_LOG_SENDTOBACKEND_HPP__
#define __UTILS_LOG_LOG_SENDTOBACKEND_HPP__

#include "../../ostream.hpp"
#include "../backend.hpp"
#include "../style.hpp"

#include <sstream>


namespace Utils::Log::Private {

    /** Prep the arguments then call the logging backend */
    template <typename... Args>
    inline void send_to_backend(Constants::CCSC id, const Level::Level lvl, const Args &...args) {
        std::ostringstream s;
        (OStream(s, args), ...);
        const std::string msg = Style::get()->str(id, lvl, s);
        Backend::get()->log(id, lvl, msg);
    }

} // namespace Utils::Log::Private

#endif
