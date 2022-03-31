/**
 * @file
 * @brief This file defines constants used throughout the API
 */
#ifndef R_API_CONSTANTS_HPP_
#define R_API_CONSTANTS_HPP_

#include <functional>
#include <pybind11/pybind11.h>

namespace API::Binder {
    /** A copy of a typedef from autogen.cpp that is needed elsewhere */
    using ModuleGetter = std::function<pybind11::module &(std::string const &)>;
} // namespace API::Binder

#endif
