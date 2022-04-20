/**
 * @file
 * \ingroup util
 * @brief This file defines a macro used to enable bitmask operators on an enum
 */
#ifndef R_SRC_UTIL_BITMASK_ENABLE_HPP_
#define R_SRC_UTIL_BITMASK_ENABLE_HPP_

#include "../macros.hpp"


/** Used to enable bitmask functionality for the given enum
 *  Warning: Because of compiler bugs, if this isn't invoked
 *  from the global namespace the compiler might throw an error
 */
#define UTIL_BITMASK_ENABLE(ENUM)                                                                  \
    /** Enable bitmask functionality for the enum given */                                         \
    template <> UTIL_ICCBOOL ::Util::BitMask::Private::enabled<ENUM> { true };


namespace Util::BitMask::Private {

    /** Disable bitmasks for all types by default */
    template <typename Enum> UTIL_ICCBOOL enabled { false };

} // namespace Util::BitMask::Private

#endif
