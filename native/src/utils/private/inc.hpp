/**
 * @file
 * @brief
 */
#ifndef __UTILS_PRIVATE_INC_HPP__
#define __UTILS_PRIVATE_INC_HPP__

#include "../../constants.hpp"

template <typename T> struct Inc {
    static constexpr Constants::Int count = 0;
    Constants::Int operator()() { return ++count; }
};


#endif
