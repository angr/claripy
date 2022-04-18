/**
 * @file
 * @brief This file defines a function to register the manually written API code
 * \ingroup api
 */
#ifndef R_API_SIGNALHANDLER_HPP_
#define R_API_SIGNALHANDLER_HPP_

#include "constants.hpp"

namespace API {
    /** Register simplify set API function */
    void signal_handler(API::Binder::ModuleGetter &m);
} // namespace API

#endif
