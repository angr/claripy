/**
 * @file
 * \ingroup utils
 * @brief This file defines the Base Log Style class
 */
#ifndef __UTILS_LOG_STYLE_BASE_HPP__
#define __UTILS_LOG_STYLE_BASE_HPP__

#include "../../../constants.hpp"
#include "../../../macros.hpp"
#include "../level.hpp"

#include <string>


namespace Utils::Log::Style {

    /** The base Log Style class
     *  All log styles must subclass this
     *  The subclass must implement the str function defined below
     */
    struct Base {
      protected:
        /** Protected pure virtual destructor */
        inline virtual ~Base() = 0;

      public:
        // Rule of 5
        SET_IMPLICITS(Base, default)

        /** Format the log message */
        virtual std::string str(Constants::CCSC log_id, const Level::Level &lvl,
                                const std::ostringstream &raw) = 0;
    };

    /** Default virtual destructor */
    Base::~Base() = default;

} // namespace Utils::Log::Style

#endif
