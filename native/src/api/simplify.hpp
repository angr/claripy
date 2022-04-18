/**
 * @file
 * @brief Define a way to store custom simplifiers
 * \ingroup api
 */
#ifndef R_API_SIMPLIFY_HPP_
#define R_API_SIMPLIFY_HPP_

#include "constants.hpp"

namespace API {
    /** Register simplify set API function */
    void simplify(API::Binder::ModuleGetter &m);
} // namespace API

#endif
