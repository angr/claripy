/**
 * @file
 * \ingroup util
 * @brief This file defines Util::sink
 */
#ifndef R_SRC_UTIL_SINK_HPP_
#define R_SRC_UTIL_SINK_HPP_


namespace Util {

    /** A function that does nothing with it's arguments
     *  This is useful if you have some parameter that is used only when DEBUG is defined but
     *  during a release build is not; in this case we could have an unused parameter warning; this
     *  struct exists to mitigate that. Normal variables can just be voided out via (void) x;
     *  but this is not true for argument packs; Util::sink can handle these.
     */
    template <typename... Args>
    [[gnu::always_inline]] static inline void sink(Args &&...) noexcept {}

} // namespace Util

#endif
