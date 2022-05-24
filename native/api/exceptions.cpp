/**
 * @file
 * \ingroup api
 */
#include "exceptions.hpp"

#include "constants.hpp"
#include "err.hpp"
#include "py_shim_code.hpp"

#include <pybind11/eval.h>
#include <src/error.hpp>

// For brevity
namespace py = pybind11;


/** register_exception but for multiple inheritance
 *  Do not use this for single inheritance, it will error
 *  Note: cepan_mi must be set first
 */
template <typename T>
auto register_exception_mi(pybind11::module_ &m, const char *const ex_name,
                           std::vector<std::string> &&pybind_qual_names,
                           std::vector<std::string> &&native_names) {
    UTIL_ASSERT(Util::Err::Usage, ((native_names.size() + pybind_qual_names.size()) >= 2),
                "This is not multiple inheritance");
    py::exec(API::py_locate_exceptions);
    // Define shim class as subclasses of parents
    std::ostringstream gen;
    gen << "type('_EMIS',(";
    for (auto &qual_name : pybind_qual_names) {
        gen << API::py_get_excp(qual_name) << ',';
    }
    for (auto &name : native_names) {
        gen << name << ',';
    }
    gen << "),{})";
    // Eval the constructed shim class, capture the PyObject *, make our exception subclass it
    return pybind11::register_exception<T>(m, ex_name, py::eval(gen.str()));
}

/** Translates a C++ exception to an existing python exception
 *  Note: this is a macro b/c this lambda must not capture to become a function pointer
 */
#define M_TRANSLATE_EXC(CPP_EXC, PY_EXC)                                                           \
    py::register_exception_translator([](std::exception_ptr p) {                                   \
        try {                                                                                      \
            if (p) {                                                                               \
                std::rethrow_exception(p);                                                         \
            }                                                                                      \
        }                                                                                          \
        catch (const CPP_EXC &e) {                                                                 \
            PyErr_SetString(PY_EXC, e.what());                                                     \
        }                                                                                          \
    })

/** Register internal Claricpp exceptions with pybind11 */
static void register_internal(py::module_ &m, const py::handle &claricpp) {
#define M_REGISTER_INTERNAL_EXC(TYPE, BASE)                                                        \
    py::register_exception<Util::Err::TYPE>(m, #TYPE, (BASE))
    // C++ exceptions; if python receives these, something went very wrong
    // Python functions do not need to plan for these, crashing should be ok
    // The base internal method, this is a fallback
    const auto internal { M_REGISTER_INTERNAL_EXC(Internal, claricpp) };
    // Collisions
    const auto collision { M_REGISTER_INTERNAL_EXC(Collision, internal) };
    M_REGISTER_INTERNAL_EXC(HashCollision, collision);
    // Directly derived classes
    // Note: some of these map to python builtin exception types
    // We choose not to map these to that, however, as these are internal claricpp exceptions
    // We thus choose to let them derive Internal instead.
    M_REGISTER_INTERNAL_EXC(Null, internal);
    M_REGISTER_INTERNAL_EXC(BadPath, internal);
    M_REGISTER_INTERNAL_EXC(Syscall, internal);
    M_REGISTER_INTERNAL_EXC(Size, internal);
    M_REGISTER_INTERNAL_EXC(Index, internal);
    M_REGISTER_INTERNAL_EXC(BadCast, internal);
    M_REGISTER_INTERNAL_EXC(BadVariantAccess, internal);
    M_REGISTER_INTERNAL_EXC(MissingVirtualFunction, internal);
    M_REGISTER_INTERNAL_EXC(Usage, internal);
    M_REGISTER_INTERNAL_EXC(RecurrenceLimit, internal);
    M_REGISTER_INTERNAL_EXC(Unknown, internal);
    M_REGISTER_INTERNAL_EXC(NotSupported, internal);
    M_REGISTER_INTERNAL_EXC(Type, internal);
}

/** Register generic python exceptions with pybind11 */
static void register_generic_python() {
    M_TRANSLATE_EXC(Util::Err::Python::Runtime, PyExc_RuntimeError); // prefer python builtin
}

/** Register claripy exceptions with pybind11 */
static void register_claripy(py::module_ &m, const py::handle &python) {
#define M_REGISTER_CLARIPY_EXC(NS, TYPE, BASE) py::register_exception<NS::TYPE>(m, #TYPE, BASE)
    // The base claripy exception; this is a fallback and useful for grouping, but should be unused
    const auto claripy { M_REGISTER_CLARIPY_EXC(Util::Err::Python, Claripy, python) };
    // Error::Backend
    namespace EBa = Error::Backend;
    M_REGISTER_CLARIPY_EXC(EBa, Abstraction, claripy);
    M_REGISTER_CLARIPY_EXC(EBa, Unsupported, claripy);
    // Error::Expr
    namespace EEx = Error::Expr;
    register_exception_mi<EEx::Value>(m, "Value", { "py_err.Claripy" }, { "ValueError" });
    register_exception_mi<EEx::Type>(m, "Type", { "py_err.Claripy" }, { "TypeError" });
    M_REGISTER_CLARIPY_EXC(EEx, Operation, claripy);
    M_REGISTER_CLARIPY_EXC(EEx, Usage, claripy);
    M_REGISTER_CLARIPY_EXC(EEx, Size, claripy);
}

/** Register API exceptions */
static void register_api(py::module_ &m, const py::handle &python) {
    auto api_m { m.def_submodule("api", "API errors") };
    const auto base { py::register_exception<API::Err::Base>(api_m, "Base", python) };
    py::register_exception<API::Err::Usage>(api_m, "Usage", base);
}

/** Bind exceptions with pybind11 */
void API::exceptions(py::module_ &root_module) {
    // Constants
    static constexpr CCSC internal_name { "_internal" };
    static constexpr CCSC py_err_name { "py_err" };
    static constexpr CCSC base_name { "Base" };
    // Modules
    auto py_err { root_module.def_submodule(py_err_name, "Python analogs of native exceptions") };
    auto internal { py_err.def_submodule(internal_name, "Claricpp internal error python analogs") };
    // Base exceptions
    // Ideally, these should not be used; they are fallbacks and useful for grouping
    const auto base { py::register_exception<Util::Err::Claricpp>(internal, base_name) };
    const auto py_e { py::register_exception<Util::Err::Python::Base>(py_err, "BasePython", base) };
    // Validation
    std::ostringstream s;
    s << root_mod_name << '.' << py_err_name << '.' << internal_name << '.' << base_name;
    const std::string cepan_mi { s.str() };
    UTIL_ASSERT(Util::Err::Unknown, API::py_cepan_mi == cepan_mi,
                "cepan_mi mismatch; report this!\nExpected: ", API::py_cepan_mi,
                "\nActual: ", cepan_mi);
    // Derived and builtin derived exceptions
    // Note: Since we *cannot* do multiple inheritance due to a limitation in the python
    // C API and thus also in pybind11, we permit some types to map to python builtin exceptions
    // Ex., Util::Err::Python::Runtime, maps to a subclass of python's RuntimeError, nothing else
    // Note, however, that we do not require it if it makes more sense not to
    register_internal(internal, base);
    register_claripy(py_err, py_e);
    register_generic_python();
    register_api(py_err, py_e);
}
