/**
 * @file
 * @brief Defines an abbreviated down-cast function
 * \ingroup unittest
 */
#ifndef __TESTS_UNIT_CREATE_DCAST_HPP__
#define __TESTS_UNIT_CREATE_DCAST_HPP__

#include "utils.hpp"


/** A dynamic down-cast alias */
template <typename T, typename U> auto dcast(const U &u) {
    return Utils::dynamic_down_cast_throw_on_fail<T>(u);
}

#endif
