/**
 * @file
 * @brief This file defines the headers binder will scan to generate bindings
 * \ingroup api
 */
#ifndef R_API_HEADERS_HPP_
#define R_API_HEADERS_HPP_

#include "src/annotation.hpp"
#include "src/backend.hpp"
#include "src/create.hpp"
#include "src/error.hpp"
#include "src/expr.hpp"
#include "src/mode.hpp"
#include "src/op.hpp"
#include "src/py_obj.hpp"

/*
 TODO: use pyrosetta stl bindings ?
 In source: replace pybind11 stl bindings header with binder's
 In config file: +binder std::vector binder::vector_binder
*/

#endif
