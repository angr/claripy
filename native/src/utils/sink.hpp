/**
 * @file
   @brief This file defines the Utils::Sink struct
 */
#ifndef __UTILS_SINK_HPP__
#define __UTILS_SINK_HPP__

#include "../macros.hpp"


/** A namespace used for the utils directory */
namespace Utils {

    /** A struct that does nothing with it's arguments
     *  This is useful if you have some parameter that is used only when DEBUG is defined but
     *  during a relase build is not; in this case we could have an unused parameter warning; this
     *  struct exists to mitigate that. Normal variables can just be voided out via (void) x;, but
     *  this is not true for argument packs; Utils::Sink can handle these. */
    struct Sink {
        /** Constructor */
        template <typename... Args> Sink(const Args &...) {}

      private:
        DELETE_DEFAULTS(Sink)
    };

} // namespace Utils

#endif
