/**
 * @file
 * \ingroup util
 * @brief This file defines a static_cast that is type-safe in debug mode
 */
#ifndef R_SRC_UTIL_CHECKEDSTATICCAST_HPP_
#define R_SRC_UTIL_CHECKEDSTATICCAST_HPP_

#include "assert.hpp"
#include "err.hpp"

#include "../macros.hpp"


namespace Util {

    /** static_cast normally, type-checked dynamic_cast if debug mode */
    template <typename Out, typename In>
    [[gnu::always_inline]] constexpr Out checked_static_cast(const In i) NOEXCEPT_UNLESS_DEBUG {
#ifdef DEBUG
        UTIL_ASSERT(Err::BadCast, dynamic_cast<Out>(i), "static cast failed.");
        return dynamic_cast<Out>(i);
#else
        return static_cast<Out>(i);
#endif
    }

} // namespace Util

#endif
