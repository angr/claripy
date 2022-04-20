/**
 * @file
 * \ingroup util
 * @brief This file defines the base logging backend class
 */
#ifndef R_SRC_UTIL_LOG_BACKEND_BASE_HPP_
#define R_SRC_UTIL_LOG_BACKEND_BASE_HPP_

#include "../../../constants.hpp"
#include "../../../macros.hpp"
#include "../../lazy_str.hpp"
#include "../level.hpp"

#include <string>


namespace Util::Log::Backend {

    /** The base backend class
     *  All Log backend must subclass this
     *  The subclass must implement the log function defined below
     */
    struct Base {
      protected:
        /** Protected pure virtual destructor */
        virtual inline ~Base() noexcept = default;

      public:
        // Rule of 5
        DEFINE_IMPLICITS_ALL_NOEXCEPT(Base);

        /** Backend name */
        virtual const char *name() const noexcept = 0;

        /** Log the given message */
        virtual void log(CCSC id, const Level::Lvl lvl, Util::LazyStr &&msg) const = 0;

        /** Flush the log if applicable */
        virtual void flush() const = 0;
    };

} // namespace Util::Log::Backend

#endif
