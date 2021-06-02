/**
 * @file
 * \ingroup utils
 * @brief This file defines a static_cast that is type-safe in debug mode
 */
#ifndef R_UTILS_CHECKEDSTATICCAST_HPP_
#define R_UTILS_CHECKEDSTATICCAST_HPP_

#include "affirm.hpp"
#include "error.hpp"

#include "../macros.hpp"


namespace Utils {

    /** static_cast normally, type-checked dynamic_cast if debug mode */
    template <typename Out, typename In>
    [[gnu::always_inline]] constexpr Out checked_static_cast(const In i) noexcept {
#ifndef DEBUG
        return static_cast<Out>(i);
#else
        affirm<Error::Unexpected::BadCast>(dynamic_cast<Out>(i) != nullptr,
                                           WHOAMI_WITH_SOURCE "static cast failed.");
        return dynamic_cast<Out>(i);
#endif
    }

} // namespace Utils

#endif
