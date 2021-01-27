/**
 * @file
 * \ingroup utils
 * @brief This file defines the base logging backend class
 */
#ifndef __UTILS_LOG_BACKEND_BASE_HPP__
#define __UTILS_LOG_BACKEND_BASE_HPP__

#include "../../../constants.hpp"
#include "../../../macros.hpp"
#include "../level.hpp"

#include <string>


namespace Utils::Log::Backend {

    /** The base backend class
     *  All Log backend must subclass this
     *  The subclass must implement the log function defined below
     */
    struct Base {

        /** Default virtual destructor */
        virtual ~Base() = 0;

        // Rule of 5
        SET_IMPLICITS(Base, default)

        /** Log the given message, level, to the correct log given by log_id */
        virtual void log(Constants::CCSC id, const Level::Level &lvl, const std::string &msg) = 0;
    };

} // namespace Utils::Log::Backend

#endif
