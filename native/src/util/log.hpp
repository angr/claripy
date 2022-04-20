/**
 * @file
 * \ingroup util
 * @brief This file includes all relevant public log members
 * Warning: Avoid logging in destructors of static objects (or anything that runs after main())
 * If a logging backend depends on std::cout, for example, since static variable destruction
 * has no predefined order this can lead to writing to a destructed std::cout
 * This may cause a segfault.
 */
#ifndef R_SRC_UTIL_LOG_HPP_
#define R_SRC_UTIL_LOG_HPP_

#include "log/backend.hpp"
#include "log/constants.hpp"
#include "log/level.hpp"
#include "log/log.hpp"
#include "log/macros.hpp"
#include "log/style.hpp"

#endif
