/**
 * @file
 * @brief This file defines the API for PyObj's
 * \ingroup api
 */
#ifndef R_SRC_API_PYOBJ_HPP_
#define R_SRC_API_PYOBJ_HPP_

#include "constants.hpp"

namespace API {
    /** Bind PyObj constructors and such */
    void py_obj(Binder::ModuleGetter &m);
} // namespace API

#endif