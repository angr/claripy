/**
 * @file
 * \ingroup util
 * @brief This file defines an unconstructable class
 */
#ifndef R_UTIL_UNCONSTRUCTABLE_HPP_
#define R_UTIL_UNCONSTRUCTABLE_HPP_

#include "../macros.hpp"


namespace Util {

    /** An unconstructable class */
    class Unconstructable {
        // Disable construction
        SET_IMPLICITS(Unconstructable, delete);
        /** Disable Destruction */
        ~Unconstructable() = delete;
    };

} // namespace Util

#endif
