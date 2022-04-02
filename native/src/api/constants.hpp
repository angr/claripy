/**
 * @file
 * @brief This file defines constants used throughout the API
 */
#ifndef R_API_CONSTANTS_HPP_
#define R_API_CONSTANTS_HPP_

#include "../constants.hpp"

#include <functional>
#include <pybind11/pybind11.h>

namespace API {
    /** The name of the root module */
    extern CCSC root_mod_name;
    namespace Binder {
        /** A copy of a typedef from autogen.cpp that is needed elsewhere
         *  An error occur during compilation of the two types differ
         */
        using ModuleGetter = std::function<pybind11::module &(std::string const &)>;
    } // namespace Binder
} // namespace API

#endif
