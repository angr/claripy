/**
 * @file
 * \ingroup utils
 * @brief This file defines the LevelTimestameMessage Log Style class
 */
#ifndef __UTILS_LOG_STYLE_LEVELTIMESTAMPMESSAGE_HPP__
#define __UTILS_LOG_STYLE_LEVELTIMESTAMPMESSAGE_HPP__

#include "abstract_base.hpp"


namespace Utils::Log::Style {

    /** A Log Style whcih prints out the log level, a timestamp, and the message */
    struct LevelTimestampMessage : public AbstractBase {

        /** Format the log message */
        std::string str(Constants::CCSC, const Level::Level &lvl,
                        const std::ostringstream &raw) override final;
    };

} // namespace Utils::Log::Style

#endif
