/**
 * @file
 * \ingroup utils
 * @brief This file defines an unconstructable class
 */
#ifndef R_UTILS_UNCONSTRUCTABLE_HPP_
#define R_UTILS_UNCONSTRUCTABLE_HPP_

#include "../macros.hpp"


namespace Utils {

    /** An unconstructable class */
    class Unconstructable {
        // Disable construction
        SET_IMPLICITS(Unconstructable, delete);
        /** Disable Destruction */
        ~Unconstructable() = delete;
    };

} // namespace Utils

#endif
