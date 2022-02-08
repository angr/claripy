/**
 * @file
 * \ingroup api
 */
#include "cpp.hpp"
#include "python_log_shim.hpp"


// Initialize to nullptr
thread_local std::exception_ptr API::exception_ptr { nullptr };


/********************************************************************/
/*                             General                              */
/********************************************************************/


/** A helper function that tries to dynamically allocate a copy of prime */
static inline char *try_gen_msg(CCSC prime) noexcept {
    char *msg { nullptr }; // NOLINT (false positive)
    try {
        const auto len { std::strlen(prime) };
        msg = new char[len + 1]; // NOLINT (non-owning memory ok, this is for C)
        if (msg != nullptr) {
            std::memcpy(msg, prime, len);
            msg[len] = 0; // NOLINT (null termination)
        }
    }
    catch (...) {
    }
    return msg;
}

/** A helper macro */
#define IS_EXCEPT(TYPE, ENUM_VALUE)                                                                \
    static_assert(Util::Type::Is::ancestor<Util::Err::Claricpp, TYPE>,                             \
                  "Must be a Claricpp error");                                                     \
    if (const auto ptr { dynamic_cast<CTSC<TYPE>>(&e) }; ptr != nullptr) {                         \
        return { .type = (ENUM_VALUE), .msg = msg, .trace = trace };                               \
    }

/** A helper function to get a python exception */
static inline ClaricppException get_py_exception(const Util::Err::Python::Base &e, CCSC msg,
                                                 CCSC trace) noexcept {

    // Error::Expr
    IS_EXCEPT(Error::Expr::Type, ClaricppExceptionEnumExprType);
    IS_EXCEPT(Error::Expr::Usage, ClaricppExceptionEnumExprUsage);
    IS_EXCEPT(Error::Expr::Value, ClaricppExceptionEnumExprValue);
    IS_EXCEPT(Error::Expr::Size, ClaricppExceptionEnumExprSize);
    IS_EXCEPT(Error::Expr::Operation, ClaricppExceptionEnumExprOperation);

    // Error::Backend
    IS_EXCEPT(Error::Backend::Abstraction, ClaricppExceptionEnumBackendAbstraction);
    IS_EXCEPT(Error::Backend::Unsupported, ClaricppExceptionEnumBackendUnsupported);

    // Fallbacks
    IS_EXCEPT(Util::Err::Python::Claripy, ClaricppExceptionEnumClaripy);
    return { .type = ClaricppExceptionEnumPython, .msg = msg, .trace = trace };
}

/** A helper function to get a C++ exception */
static inline ClaricppException get_cpp_exception(const Util::Err::Unexpected &, CCSC msg,
                                                  CCSC trace) noexcept {
    // Fallback
    return { .type = ClaricppExceptionEnumUnexpected, .msg = msg, .trace = trace };
}

/** A helper function that tries to get the exception the last API call threw */
static inline ClaricppException get_exception() noexcept {
    try {
        if (LIKELY(API::exception_ptr)) {
            // Re-throw exception so we can catch it
            std::rethrow_exception(API::exception_ptr);
        }
        // No exception (just in case)
        return { .type = ClaricppExceptionEnumNone, .msg = nullptr, .trace = nullptr };
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
                return get_py_exception(*py, msg, trace);
            }
            // Unexpected
            else if (CppE cpp { dynamic_cast<CppE>(ce) }; LIKELY(cpp != nullptr)) {
                return get_cpp_exception(*cpp, msg, trace);
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

/** A static global to allow converting the python function into a function pointer */
ClaricppSimp global_py_simp { nullptr };

static Expr::BasePtr simp_wrapper(const Expr::BasePtr &e) {
    ClaricppExpr in { API::copy_to_c(e) };
    ClaricppExpr out { global_py_simp(in) };
    if (in.ptr != out.ptr) { // Python would handle this via reference counting
        API::free(in);
    }
    Expr::BasePtr ret { std::move(API::to_cpp(out)) };
    API::free(out); // Clean up after python stuff
    return ret;
}

// @todo: test cases?
extern "C" {
    void claricpp_init_for_python_usage(PyStr src, ClaricppPyLog py_log, ClaricppPyLevel py_lvl,
                                        ClaricppSimp py_simp) {
        // This should only be called once
        static bool first { true };
        UTIL_ASSERT(Util::Err::Usage, first, "This function should only be called once!");
        first = false;

        // Backward init
        Util::Log::info("Enabling claricpp backtraces");
        Util::Err::Claricpp::toggle_backtrace(true);
        if (src == nullptr) {
            Util::Log::warning(
                "Backward has not been given source, backtraces will not include source snippits!");
        }
        else {
            Util::Log::info("Adding source root to backward search path");
            Util::Backtrace::backward_add_source_root(src);
        }

        // Log backend
        Util::Log::info("Installing Python logging backend");
        Util::Log::Backend::set<API::PythonLogShim>(py_log, py_lvl);

        // Log levels
        Util::Log::info(
            "Configuring Claricpp to send all logs to allow Python to handle log levels.");
        Util::Log::Level::set(Util::Log::Level::Level::Verbose);

        // Simplifiers
        if (py_simp != nullptr) {
            Util::Log::info("Installing Python simplifier");
            global_py_simp = py_simp;
            Simplify::manager.register_(simp_wrapper);
        }

        // Success
        Util::Log::info("Claricpp successfully configured for python usage");
    }

    BOOL claricpp_has_exception() {
        try {
            return API::bool_(bool { API::exception_ptr });
        }
        catch (...) {
            Util::terminate("has_exception failed");
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
            return {
                .type = ClaricppExceptionEnumFailAlloc,
                .msg = try_gen_msg(
                    "Got std::bad_alloc within get_exception while processing another exception"),
                .trace = nullptr
            };
        }
        catch (...) {
            return { .type = ClaricppExceptionEnumFailCritical,
                     .msg = try_gen_msg("get_exception failed for unknown reason"),
                     .trace = nullptr };
        }
    }
}


/********************************************************************/
/*                          Free Functions                          */
/********************************************************************/


/** A local macro used for consistency */
#define DEFINE_FREE_FUNC(TYPE, NAME)                                                               \
    void claricpp_free_##NAME(TYPE *const c_object) {                                              \
        API_FUNC_START                                                                             \
        UTIL_ASSERT_NOT_NULL_DEBUG(c_object);                                                      \
        API::free(*c_object);                                                                      \
        API_FUNC_END_NO_RETURN                                                                     \
    }

/** A local macro used for consistency */
#define DEFINE_ARR_FREE_FUNC(TYPE, NAME)                                                           \
    void claricpp_free_array_##NAME(ARRAY_OUT(TYPE) *const c_array) {                              \
        API_FUNC_START                                                                             \
        UTIL_ASSERT_NOT_NULL_DEBUG(c_array);                                                       \
        API::free<true>(*c_array);                                                                 \
        API_FUNC_END_NO_RETURN                                                                     \
    }

/** A local macro used for consistency */
#define DEFINE_DOUBLE_ARR_FREE_FUNC(TYPE, NAME)                                                    \
    void claricpp_free_double_array_##NAME(DOUBLE_ARRAY_OUT(TYPE) *const c_array) {                \
        API_FUNC_START                                                                             \
        UTIL_ASSERT_NOT_NULL_DEBUG(c_array);                                                       \
        API::free<2>(*c_array);                                                                    \
        API_FUNC_END_NO_RETURN                                                                     \
    }

extern "C" {
    void claricpp_free_str(char *const s) { delete s; }

    // Unions
    DEFINE_FREE_FUNC(ClaricppPrim, prim);
    DEFINE_FREE_FUNC(ClaricppArg, arg);

    // Structs
    DEFINE_FREE_FUNC(ClaricppException, exception);
    DEFINE_FREE_FUNC(ClaricppAnnotation, annotation);
    DEFINE_FREE_FUNC(ClaricppSPAV, spav);
    DEFINE_FREE_FUNC(ClaricppExpr, expr);
    DEFINE_FREE_FUNC(ClaricppBackend, backend);
    DEFINE_FREE_FUNC(ClaricppSolver, solver);

    // Arrays
    DEFINE_ARR_FREE_FUNC(ClaricppAnnotation, annotation);
    DEFINE_ARR_FREE_FUNC(ClaricppExpr, expr);
    DEFINE_ARR_FREE_FUNC(ClaricppPrim, prim);
    DEFINE_ARR_FREE_FUNC(ClaricppArg, arg);

    // Doubles Arrays
    DEFINE_DOUBLE_ARR_FREE_FUNC(ClaricppPrim, prim);
}

// Cleanup
#undef DEFINE_FREE_FUNC
#undef DEFINE_ARR_FREE_FUNC
#undef DEFINE_DOUBLE_ARR_FREE_FUNC