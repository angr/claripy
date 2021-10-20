/**
 * @file
 * \ingroup util
 * @brief This file defines the Base Log Style class
 */
#ifndef R_UTIL_LOG_STYLE_BASE_HPP_
#define R_UTIL_LOG_STYLE_BASE_HPP_

#include "../../../constants.hpp"
#include "../../../macros.hpp"
#include "../level.hpp"

#include <string>


namespace Util::Log::Style {

    /** The base Log Style class
     *  All log styles must subclass this
     *  The subclass must implement the str function defined below
     */
    struct Base {
      protected:
        /** Protected pure virtual destructor */
        inline virtual ~Base() noexcept = 0;

      public:
        // Rule of 5
        DEFINE_IMPLICITS_ALL_NOEXCEPT(Base);

        /** Format the log message */
        virtual std::string str(CCSC log_id, const Level::Level &lvl,
                                const std::ostringstream &raw) const = 0;
    };

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Util::Log::Style

#endif
