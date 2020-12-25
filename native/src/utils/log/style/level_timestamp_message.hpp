/**
 * @file
 * @brief This file defines the LevelTimestameMessage style
 */
#ifndef __UTILS_LOG_STYLE_LEVELTIMESTAMPMESSAGE_HPP__
#define __UTILS_LOG_STYLE_LEVELTIMESTAMPMESSAGE_HPP__

#include "abstract_base.hpp"


namespace Utils::Log::Style {

    /** The default log style class */
    struct LevelTimestampMessage : public AbstractBase {
        /** Format the log message */
        std::string operator()(const Level &lvl, std::ostringstream &raw) const override final;
    };

} // namespace Utils::Log::Style

#endif
