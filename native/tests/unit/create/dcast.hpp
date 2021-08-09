/**
 * @file
 * @brief Defines an abbreviated down-cast function
 * \ingroup unittest
 */
#ifndef R_UNIT_CREATE_DCAST_HPP_
#define R_UNIT_CREATE_DCAST_HPP_

#include "utils.hpp"


/** A dynamic down-cast alias */
template <typename T, typename U> auto dcast(const U &u) {
    return Utils::Cast::Dynamic::down_throw_on_fail<T>(u);
}

#endif
