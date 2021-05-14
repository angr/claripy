/**
 * @file
 * \ingroup utils
 * @brief This file defines the default Log Backend
 */
#ifndef R_UTILS_LOG_BACKEND_DEFAULT_HPP_
#define R_UTILS_LOG_BACKEND_DEFAULT_HPP_

#include "clog.hpp"


namespace Utils::Log::Backend {

    /** Define the default Log backend
     *  This must be default constructable
     */
    using Default = Clog;

} // namespace Utils::Log::Backend

#endif
