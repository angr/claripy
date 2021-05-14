/**
 * @file
 * \ingroup utils
 * @brief This file defines the base logging backend class
 */
#ifndef R_UTILS_LOG_BACKEND_BASE_HPP_
#define R_UTILS_LOG_BACKEND_BASE_HPP_

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
      protected:
        /** Protected pure virtual destructor */
        virtual inline ~Base() noexcept = 0;

      public:
        // Rule of 5
        SET_IMPLICITS(Base, default)

        /** Log the given message, level, to the correct log given by log_id */
        virtual void log(Constants::CCSC id, const Level::Level &lvl,
                         const std::string &msg) const = 0;
    };

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Utils::Log::Backend

#endif
