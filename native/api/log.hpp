/**
 * @file
 * @brief This file defines a method to link the Python and C++ logging systems together
 * \ingroup api
 */
#ifndef R_API_LOG_HPP_
#define R_API_LOG_HPP_

#include "constants.hpp"

namespace API {
    /** Register log init API function */
    void logger(API::Binder::ModuleGetter &m);
} // namespace API

#endif
