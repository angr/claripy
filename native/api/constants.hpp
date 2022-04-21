/** \defgroup api Claricpp Python API
 * @brief A group of files which define the python API
 */

/**
 * @file
 * @brief This file defines constants used throughout the API
 * \ingroup api
 */
#ifndef R_API_CONSTANTS_HPP_
#define R_API_CONSTANTS_HPP_

#include <functional>
#include <pybind11/pybind11.h>
#include <src/constants.hpp>

namespace API {

    /** The name of the root module */
    extern CCSC root_mod_name;
    namespace Binder {
        /** A copy of a typedef from autogen.cpp that is needed elsewhere
         *  An error occur during compilation of the two types differ
         */
        using ModuleGetter = std::function<pybind11::module &(std::string const &)>;
    } // namespace Binder

    /** Use to register a function to run on exit; do this for *every* callback!
     *  Callbacks are python objects, when python exits python may choose to finalize
     *  them before C++ desturctors are called, leading to dangling references and segfaults
     *  These functions will be called at exit, but before python finalizers
     */
    inline void register_at_exit(void (*const func)() noexcept) {
        pybind11::module_::import("atexit").attr("register")(pybind11::cpp_function(func));
    }

} // namespace API

#endif
