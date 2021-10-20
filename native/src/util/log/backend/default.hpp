/**
 * @file
 * \ingroup util
 * @brief This file defines the default Log Backend
 */
#ifndef R_UTIL_LOG_BACKEND_DEFAULT_HPP_
#define R_UTIL_LOG_BACKEND_DEFAULT_HPP_

#include "clog.hpp"


namespace Util::Log::Backend {

    /** Define the default Log backend
     *  This must be default constructable
     */
    using Default = Clog;

} // namespace Util::Log::Backend

#endif
