/**
 * @file
 * @brief This file defines the default Log Backend
 */
#ifndef __UTILS_LOG_BACKEND_DEFAULT_HPP__
#define __UTILS_LOG_BACKEND_DEFAULT_HPP__

#include "cout.hpp"


namespace Utils::Log::Backend {

    /** Define the default Log backend */
    using Default = Cout;

} // namespace Utils::Log::Backend

#endif
