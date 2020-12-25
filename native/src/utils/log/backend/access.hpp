/**
 * @file
 * @brief This file methods for accessing the Log Backend
 */
#ifndef __UTILS_LOG_BACKEND_ACCESS_HPP__
#define __UTILS_LOG_BACKEND_ACCESS_HPP__

#include "abstract_base.hpp"


namespace Utils::Log::Backend {

    /** Set the Log backend by copy */
    void set(AbstractBase b);

    /** Return a copy of the backend */
    AbstractBase get();

} // namespace Utils::Log::Backend

#endif
