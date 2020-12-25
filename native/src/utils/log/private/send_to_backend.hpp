/**
 * @file
 * @brief This file defines a function which preps its args then sends them to the Log Backend
 */
#ifndef __UTILS_LOG_LOG_SENDTOBACKEND_HPP__
#define __UTILS_LOG_LOG_SENDTOBACKEND_HPP__

#include "../../to_str.hpp"
#include "../backend.hpp"
#include "../style.hpp"


namespace Utils::Log::Private {

    /** Prep the arguments then call the logging backend */
    template <typename... Args>
    void send_to_backend(Constants::CCSC id, const Level lvl, const Args &...args) {
        std::ostringstream s;
        apply_to_ostringstream(s, args...);
        const std::string msg = Style::get()->str(id, lvl, s);
        Backend::get()->log(id, lvl, msg);
    }

} // namespace Utils::Log::Private

#endif
