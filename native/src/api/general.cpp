/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"

// Initialize to nullptr
thread_local const std::exception *API::exception_ptr { nullptr };

void claricpp_init_for_python_usage() {}

BOOL claricpp_has_exception() {
    return API::exception_ptr != nullptr;
}

ClaricppException claricpp_get_excption() {
    using CE = CTSC<Util::Err::Claricpp>;
    // No exception (just in case)
    if (UNLIKELY(API::exception_ptr == nullptr)) {
        return { .type = ClaricppExceptionEnumNone, .msg = nullptr, .trace = nullptr };
    }
    // Claricpp exception
    else if (CE ce { dynamic_cast<CE>(API::exception_ptr) }; ce != nullptr) {
        const char * msg { API::c_str(ce->what(), std::strlen(ce->what()) };
        const char *trace { API::c_str(ce->backtrace()) };
        using PyE = CTSC<Util::Err::Python::Claripy>;
        using CppE = CTSC<Util::Err::Unexpected>;
        // Python analog
        if (PyE py { dynamic_cast<PyE>(ce) }; LIKELY(py != nullptr)) {
            return { .type = ClaricppExceptionEnumPython, .msg = msg, .trace = trace };
        }
        else if (CppE cpp { dynamic_cast<CppE>(ce) }; LIKELY(cpp != nullptr)) {
            return { .type = ClaricppExceptionEnumUnexpected, .msg = msg, .trace = trace };
        }
        else {
            return { .type = ClaricppExceptionEnumUnknown, .msg = msg, .trace = trace };
        }
    }
    // std::exception
    else {
        CCSC what { API::exception_ptr->what() };
        const char *msg { API::c_str(what, std::strlen(what)) };
        return { .type = ClaricppExceptionEnumStd, .msg = msg, .trace = nullptr };
    }
}
