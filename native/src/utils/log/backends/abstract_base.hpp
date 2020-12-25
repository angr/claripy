/**
 * @file
 * @brief This file defines the base logging backend class
 */
#ifndef __UTILS_LOG_BACKEND_ABSTRACTBASE_HPP__
#define __UTILS_LOG_BACKEND_ABSTRACTBASE_HPP__

#include "../../../constants.hpp"
#include "../level.hpp"


namespace Utils::Log::Backend {

    /** The base backend class
     *  All Log backend must subclass this
     *  The subclass must implement the log function defined below
     */
    struct AbstractBase {

        /** Default virtual destructor */
        virtual ~AbstractBase() = default;

        /** Log the given message, level, to the correct log given by log_id */
        virtual void log(Constants::CCSC id, const Level &lvl, const std::string &msg) = 0;
    };

} // namespace Utils::Log::Backend

#endif
