/**
 * @file
 * @brief This file defines python code used for backtrace API functions
 * \ingroup api
 */
#ifndef R_BACKTRACE_HPP_
#define R_BACKTRACE_HPP_

#include "constants.hpp"

namespace API {

    /** Generate API::set_source_root for the python API
     *  Allows the user to set the source root for backtraces
     */
    void backtrace(API::Binder::ModuleGetter &m);

} // namespace API

#endif