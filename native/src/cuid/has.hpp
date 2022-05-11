/**
 * @file
 * @brief This file defines a way to check if a class has a static CUID
 */
#ifndef R_SRC_CUID_HAS_HPP_
#define R_SRC_CUID_HAS_HPP_

#include "../util.hpp"

namespace CUID {
    /** True only if T has a static_cuid */
    UTIL_TYPE_SFINAETEST(has_static_cuid, T::static_cuid, typename T);
} // namespace CUID

#endif