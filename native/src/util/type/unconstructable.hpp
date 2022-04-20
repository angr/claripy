/**
 * @file
 * \ingroup util
 * @brief This file defines an unconstructable class
 */
#ifndef R_SRC_UTIL_TYPE_UNCONSTRUCTABLE_HPP_
#define R_SRC_UTIL_TYPE_UNCONSTRUCTABLE_HPP_

#include "../../macros.hpp"


namespace Util::Type {

    /** An unconstructable class */
    class Unconstructable {
        // Disable construction
        SET_IMPLICITS(Unconstructable, delete);
        /** Disable Destruction */
        ~Unconstructable() = delete;
    };

} // namespace Util::Type

#endif
