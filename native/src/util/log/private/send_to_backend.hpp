/**
 * @file
 * \ingroup util
 * @brief This file defines a function which preps its args then sends them to the Log Backend
 */
#ifndef R_SRC_UTIL_LOG_PRIVATE_SENDTOBACKEND_HPP_
#define R_SRC_UTIL_LOG_PRIVATE_SENDTOBACKEND_HPP_

#include "../backend.hpp"
#include "../style.hpp"


namespace Util::Log::Private {

    /** Prep the arguments then call the logging backend */
    inline void send_to_backend(CCSC id, const Level::Lvl lvl, Util::LazyStr &&msg) {
        UTIL_ASSERT_NOT_NULL_DEBUG(Style::get());   // Sanity check
        UTIL_ASSERT_NOT_NULL_DEBUG(Backend::get()); // Sanity check
        Backend::get()->log(id, lvl, std::move(msg));
    }

} // namespace Util::Log::Private

#endif
