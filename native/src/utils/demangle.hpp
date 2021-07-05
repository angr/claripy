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
#include <string>
#include <type_traits>


namespace Utils {

    /** Demangle a C++ name-mangled symbol */
    inline std::string demangle(Constants::CCSC mangled) {
        int status { -1 };     // NOLINT Status: Failure
        std::size_t len { 0 }; // NOLINT
        auto *buf { abi::__cxa_demangle(mangled, nullptr, &len, &status) };
        namespace Err = Utils::Error::Unexpected;
        if (status == 0) {
            std::string ret { buf, len };
            std::free(buf); // NOLINT
            return ret;
        }
        std::free(buf); // NOLINT
        switch (status) {
            case -1:
                throw std::bad_alloc();
            case -2:
                throw Err::Unknown("Demangling failed for: ", mangled);
            case -3:
                throw Err::Usage(WHOAMI_WITH_SOURCE);
            default:
                throw Err::Unknown(WHOAMI_WITH_SOURCE "Impossible return value");
        };
    }

    /** noexcept Demangle a C++ name-mangled symbol, on failure returns mangled */
    inline std::string try_demangle(Constants::CCSC mangled) noexcept {
        try {
            return demangle(mangled);
        }
        catch (Utils::Error::Claricpp &) {
            return mangled;
        }
    }

} // namespace Utils

#endif
