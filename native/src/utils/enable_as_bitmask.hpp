/**
 * @file
 * \ingroup utils
 * @brief This file defines a macro used to enable bitmask operators on an enum
 */
#ifndef __UTILS_ENABLE_AS_BITMASK_HPP__
#define __UTILS_ENABLE_AS_BITMASK_HPP__

#include "macros.hpp"


namespace Utils {

/** Used to enable bitmask functionality for the given enum
 *  Warning: Because of compiler bugs, if this isn't invoked
 *  from the global namespace the compiler might throw an error
 */
#define ENABLE_AS_BITMASK(ENUM)                                                                   \
    /** Enable bitmask functionality for the enum given */                                        \
    template <> UTILS_ICCBOOL ::Utils::bitmask_enabled<ENUM> { true };

    /** Disable bitmasks for all types by default */
    template <typename Enum> UTILS_ICCBOOL bitmask_enabled { false };

} // namespace Utils

#endif
