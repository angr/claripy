/**
 * @file
 * \ingroup util
 * @brief This file defines the Base Log Style class
 */
#ifndef R_SRC_UTIL_LOG_STYLE_BASE_HPP_
#define R_SRC_UTIL_LOG_STYLE_BASE_HPP_

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

        /** Style name */
        virtual const char *name() const noexcept = 0;

        /** Format the log message */
        virtual std::string str(CCSC log_id, const Level::Lvl lvl, std::string &&raw) const = 0;
    };

    /** Default virtual destructor */
    Base::~Base() noexcept = default;

} // namespace Util::Log::Style

#endif
