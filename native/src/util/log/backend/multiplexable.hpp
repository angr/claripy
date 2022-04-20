/**
 * @file
 * \ingroup util
 * @brief This file defines an abstract multiplexable log backend
 */
#ifndef R_SRC_UTIL_LOG_BACKEND_MULTIPLEXABLE_HPP_
#define R_SRC_UTIL_LOG_BACKEND_MULTIPLEXABLE_HPP_

#include "base.hpp"


namespace Util::Log::Backend {
    /** A backend suitable to be multiplexed */
    struct Multiplexable : public Base {
        /** Log the given message */
        virtual void log_str(CCSC id, const Level::Lvl lvl, std::string &&msg) const = 0;
    };
} // namespace Util::Log::Backend

#endif
