/**
 * @file
 * @brief This file defines a function to link Python and C++ exceptions
 * \ingroup api
 */
#ifndef R_SRC_API_EXCEPTIONS_HPP_
#define R_SRC_API_EXCEPTIONS_HPP_

#include <pybind11/pybind11.h>

namespace API {
    /** Register exceptions with pybind11 */
    void exceptions(pybind11::module_ &);
} // namespace API

#endif
