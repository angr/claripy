/**
 * @file
   @brief This file defines Utils::sink
 */
#ifndef __UTILS_SINK_HPP__
#define __UTILS_SINK_HPP__


/** A namespace used for the utils directory */
namespace Utils {

    /** A function that does nothing with it's arguments
     *  This is useful if you have some parameter that is used only when DEBUG is defined but
     *  during a relase build is not; in this case we could have an unused parameter warning; this
     *  struct exists to mitigate that. Normal variables can just be voided out via (void) x;, but
     *  this is not true for argument packs; Utils::sink can handle these. */
    template <typename... Args> [[gnu::always_inline]] inline void sink(const Args &...) {}

} // namespace Utils

#endif
