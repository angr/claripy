/**
 * @file
 * \ingroup utils
 * @brief This file defines a macro used to enable bitmask operators on an enum
 */
#ifndef R_UTILS_BITMASK_ENABLE_HPP_
#define R_UTILS_BITMASK_ENABLE_HPP_

#include "../macros.hpp"


/** Used to enable bitmask functionality for the given enum
 *  Warning: Because of compiler bugs, if this isn't invoked
 *  from the global namespace the compiler might throw an error
 */
#define UTILS_BITMASK_ENABLE(ENUM)                                                                \
    /** Enable bitmask functionality for the enum given */                                        \
    template <> UTILS_ICCBOOL ::Utils::BitMask::Private::enabled<ENUM> { true };


namespace Utils::BitMask::Private {

    /** Disable bitmasks for all types by default */
    template <typename Enum> UTILS_ICCBOOL enabled { false };

} // namespace Utils::BitMask::Private

#endif
