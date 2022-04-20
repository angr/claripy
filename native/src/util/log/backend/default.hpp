/**
 * @file
 * \ingroup util
 * @brief This file defines the default Log Backend
 */
#ifndef R_SRC_UTIL_LOG_BACKEND_DEFAULT_HPP_
#define R_SRC_UTIL_LOG_BACKEND_DEFAULT_HPP_

#include "cerr.hpp"


namespace Util::Log::Backend {

    /** Define the default Log backend
     *  This must be default constructable
     */
    using Default = Cerr;

} // namespace Util::Log::Backend

#endif
