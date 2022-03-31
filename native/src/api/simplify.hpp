/**
 * @file
 * @brief Define a way to store custom simplifiers
 */
#ifndef R_API_SIMPLIFY_HPP_
#define R_API_SIMPLIFY_HPP_

#include "constants.hpp"

namespace API {
    /** Register simplify set API function */
    void bind_simplify_init(API::Binder::ModuleGetter &m);
} // namespace API

#endif
