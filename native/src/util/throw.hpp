/**
 * @file
 * \ingroup util
 * @brief This file defines a macro to throw an excpetion prepended with WHOAMI
 */
#ifndef R_SRC_UTIL_THROW_HPP_
#define R_SRC_UTIL_THROW_HPP_

#include "to_str.hpp"

#include "../macros.hpp"


/** A convenient way to throw an exception, msg = WHOAMI */
#define UTIL_THROW_EMPTY(E_TYPE)                                                                   \
    { throw E_TYPE { Util::to_str(WHOAMI) }; }

/** A convenient way to throw an exception, prepends WHOAMI to ... */
#define UTIL_THROW(E_TYPE, ...)                                                                    \
    { throw E_TYPE { Util::to_str(WHOAMI, __VA_ARGS__) }; }


#endif