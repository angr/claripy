/**
 * @file
 * \ingroup utils
 * @brief This file defines Utils::sink
 */
#ifndef R_UTILS_SINK_HPP_
#define R_UTILS_SINK_HPP_


namespace Utils {

    /** A function that does nothing with it's arguments
     *  This is useful if you have some parameter that is used only when DEBUG is defined but
     *  during a relase build is not; in this case we could have an unused parameter warning; this
     *  struct exists to mitigate that. Normal variables can just be voided out via (void) x;, but
     *  this is not true for argument packs; Utils::sink can handle these. */
    template <typename... Args>
    [[gnu::always_inline]] static inline void sink(const Args &...) noexcept {}

} // namespace Utils

#endif
