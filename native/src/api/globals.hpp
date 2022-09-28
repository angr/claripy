/**
 * @file
 * @brief Register global variables as binder doesn't grab them
 * \ingroup api
 */
#ifndef R_SRC_API_GLOBALS_HPP_
#define R_SRC_API_GLOBALS_HPP_

#include "constants.hpp"

namespace API {
    /** Register globals with pybind11 */
    void globals(API::Binder::ModuleGetter &m);
} // namespace API

#endif
