/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"


// Initialize to nullptr
thread_local std::exception_ptr API::exception_ptr { nullptr };


void claricpp_init_for_python_usage() {}

BOOL claricpp_has_exception() {
    return API::bool_(API::exception_ptr ? true : false);
}


/** A helper function that tries to dynamically allocate a copy of prime */
static inline char *try_gen_msg(CCSC prime) noexcept {
    char *msg { nullptr };
    try {
        msg = new char[std::strlen(prime) + 1];
        if (msg != nullptr) {
            std::strcpy(msg, prime);
        }
    }
    catch (std::exception &) {
    }
    return msg;
}

/** A helper function that tries to get the exception the last API call threw */
static inline ClaricppException get_exception() noexcept {
    // No exception (just in case)
    try {
        if (LIKELY(API::exception_ptr)) {
            std::rethrow_exception(API::exception_ptr);
        }
        // No exception
        else {
            return { .type = ClaricppExceptionEnumNone, .msg = nullptr, .trace = nullptr };
        }
    }
    catch (const std::exception &e) {
        const char *msg { API::c_str(e.what(), std::strlen(e.what())) };
        // Claricpp exception
        using CE = CTSC<Util::Err::Claricpp>;
        if (CE ce { dynamic_cast<CE>(&e) }; LIKELY(ce != nullptr)) {
            const char *trace { API::c_str(ce->backtrace()) };
            using PyE = CTSC<Util::Err::Python::Claripy>;
            using CppE = CTSC<Util::Err::Unexpected>;
            // Python analog
            if (PyE py { dynamic_cast<PyE>(ce) }; LIKELY(py != nullptr)) {
                return { .type = ClaricppExceptionEnumPython, .msg = msg, .trace = trace };
            }
            // Unexpected
            else if (CppE cpp { dynamic_cast<CppE>(ce) }; LIKELY(cpp != nullptr)) {
                return { .type = ClaricppExceptionEnumUnexpected, .msg = msg, .trace = trace };
            }
            // This should never happen
            else {
                return { .type = ClaricppExceptionEnumUnknown, .msg = msg, .trace = trace };
            }
        }
        // std::exception
        else {
            return { .type = ClaricppExceptionEnumStd, .msg = msg, .trace = nullptr };
        }
    }
}


ClaricppException claricpp_get_exception() {
    try {
        return get_exception();
    }
    catch (std::exception &e) {
        return { .type = ClaricppExceptionEnumUnknownCritical,
                 .msg = try_gen_msg("get_exception failed; please crash"),
                 .trace = nullptr };
    }
}
