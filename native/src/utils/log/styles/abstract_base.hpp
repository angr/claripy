/**
 * @file
 * @brief This file defines the AbstractBase Log Style class
 */
#ifndef __UTILS_LOG_STYLE_ABSTRACTBASE_HPP__
#define __UTILS_LOG_STYLE_ABSTRACTBASE_HPP__

#include "../../../constants.hpp"
#include "../level.hpp"

#include <string>


namespace Utils::Log::Style {

    /** The base Log Style class
     *  All log styles must subclass this
     *  The subclass must implement the str function defined below
     */
    struct AbstractBase {

        /** Default virtual destructor */
        virtual ~AbstractBase() = default;

        /** Format the log message */
        virtual std::string str(Constants::CCSC log_id, const Level &lvl,
                                const std::ostringstream &raw) = 0;
    };

} // namespace Utils::Log::Style

#endif
