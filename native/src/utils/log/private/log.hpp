/**
 * @file
 * @brief This file defines a private logging which preps the arguments for the log backend
 */
#ifndef __UTILS_LOG_LOG_LOG_HPP__
#define __UTILS_LOG_LOG_LOG_HPP__

#include "../../../constants.hpp"
#include "../../apply.hpp"
#include "../../private/ostream.hpp"
#include "../backend.hpp"
#include "../level.hpp"
#include "../style.hpp"

#include <sstream>


namespace Utils::Log::Private {

    /** Prep the arguments then call the logging backend */
    template <typename... Args>
    void backend(Constants::CCSC id, const Level lvl, const Args &...args) {
        std::ostringstream s;
        apply<::Utils::Private::OStreamConst>(s, args...);
        const std::string msg = Style::get()->str(id, lvl, s);
        Backend::get()->log(id, lvl, msg);
    }

} // namespace Utils::Log::Private

#endif
