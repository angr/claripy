/**
 * @file
 * \ingroup utils
 * @brief This file defines a method of demangling C++ name-mangled symbols
 */
#ifndef R_UTILS_DEMANGLE_HPP_
#define R_UTILS_DEMANGLE_HPP_

#include "affirm.hpp"
#include "error.hpp"

#include "../constants.hpp"

#include <cxxabi.h>
#include <iostream>
#include <stdexcept>
#include <string>
#include <type_traits>

namespace Utils {

    /** Demangle a C++ name-mangled symbol */
    inline std::string demangle(CCSC mangled) {
        int status { -1 }; // NOLINT Status: Failure
        auto *buf { abi::__cxa_demangle(mangled, nullptr, nullptr, &status) };
        namespace Err = Utils::Error::Unexpected;
        if (status == 0) {
            std::string ret { buf };
            std::free(buf); // NOLINT
            return ret;
        }
        std::free(buf); // NOLINT
        switch (status) {
            case -1:
                throw std::bad_alloc();
            case -2:
                throw std::runtime_error("Demangling failed.");
            case -3:
                throw Err::Usage(WHOAMI_WITH_SOURCE);
            default:
                throw Err::Unknown(WHOAMI_WITH_SOURCE "Impossible return value");
        };
    }

    /** noexcept Demangle a C++ name-mangled symbol, on failure returns mangled */
    inline std::string try_demangle(CCSC mangled) noexcept {
        try {
            return demangle(mangled);
        }
        catch (Utils::Error::Claricpp &) {
            return mangled;
        }
        catch (std::runtime_error &) {
            return mangled;
        }
    }

} // namespace Utils

#endif
