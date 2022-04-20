/**
 * @file
 * \ingroup util
 * @brief This file defines a method of demangling C++ name-mangled symbols
 */
#ifndef R_SRC_UTIL_DEMANGLE_HPP_
#define R_SRC_UTIL_DEMANGLE_HPP_

#include "assert.hpp"
#include "err.hpp"

#include "../constants.hpp"

#include <cxxabi.h>
#include <iostream>
#include <stdexcept>
#include <string>
#include <type_traits>

namespace Util {

    /** Demangle a C++ name-mangled symbol */
    inline std::string demangle(CCSC mangled) {
        int status { -1 }; // NOLINT Status: Failure
        auto *buf { abi::__cxa_demangle(mangled, nullptr, nullptr, &status) };
        namespace Err = Util::Err;
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
                UTIL_THROW(std::runtime_error, "Demangling failed.");
            case -3:
                UTIL_THROW(Err::Usage, "__cxa_demangle failed");
            default:
                UTIL_THROW(Err::Unknown, "Impossible return value");
        };
    }

    /** noexcept Demangle a C++ name-mangled symbol, on failure returns mangled */
    inline std::string try_demangle(CCSC mangled) noexcept {
        try {
            return demangle(mangled);
        }
        catch (Util::Err::Claricpp &) {
            return mangled;
        }
        catch (std::runtime_error &) {
            return mangled;
        }
    }

} // namespace Util

#endif
