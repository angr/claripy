/**
 * @file
 * \ingroup util
 * @brief This file defines the LevelTimestampMessage Log Style class
 */
#ifndef R_UTIL_LOG_STYLE_LEVELTIMESTAMPMESSAGE_HPP_
#define R_UTIL_LOG_STYLE_LEVELTIMESTAMPMESSAGE_HPP_

#include "base.hpp"


namespace Util::Log::Style {

    /** A Log Style which prints out the log level, a timestamp, and the message */
    struct LevelTimestampMessage final : public Base {
        /** Style name */
        inline CCSC name() const noexcept override { return "LevelTimestampMessage"; }
        /** Format the log message */
        std::string str(CCSC, const Level::Level &lvl, std::string &&raw) const final;
    };

} // namespace Util::Log::Style

#endif
