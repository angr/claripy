/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"
#include "python_log_shim.hpp"


// Initialize to nullptr
thread_local std::exception_ptr API::exception_ptr { nullptr };

// @todo: test cases?

void claricpp_init_for_python_usage(ClaricppPyLog py_log, ClaricppPyLevel py_lvl) {
    Util::Log::info("Installing Python logging backend");
    Util::Log::Backend::set<API::PythonLogShim>(py_log, py_lvl);

    Util::Log::info("Configuring Claricpp to send all logs to allow Python to handle log levels.");
    Util::Log::Level::set(Util::Log::Level::Level::Verbose);

    Util::Log::info("Claricpp successfully configured for python usage");
}

BOOL claricpp_has_exception() {
    try {
        return API::bool_(API::exception_ptr);
    }
    catch (...) {
        Util::terminate("has_exception failed");
    }
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
    catch (...) {
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
    // Exempt from need of API_FUNC_START and such
    static_assert(noexcept(API::exception_ptr = nullptr), "Should be noexcept");
    try {
        const auto ret { get_exception() };
        API::exception_ptr = nullptr;
        return ret;
    }
    catch (std::bad_alloc &) {
        return { .type = ClaricppExceptionEnumFailAlloc,
                 .msg = try_gen_msg("Got std::bad_alloc within get_exception"),
                 .trace = nullptr };
    }
    catch (...) {
        return { .type = ClaricppExceptionEnumFailCritical,
                 .msg = try_gen_msg("get_exception failed for unknown reason"),
                 .trace = nullptr };
    }
}
