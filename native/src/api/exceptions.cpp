#include "exceptions.hpp"

#include "constants.hpp"

#include "../error.hpp"

#include <pybind11/eval.h>

// For brevity
namespace py = pybind11;


/** register_exception but for multiple inheritance
 *  Do not use this for single inheritance, it will error
 */
template <typename T>
auto register_exception_mi(pybind11::module_ &m, const char *const ex_name,
                           std::vector<std::string> &&pybind_qual_names,
                           std::vector<std::string> &&native_names) {
    UTIL_ASSERT(Util::Err::Usage, ((native_names.size() + pybind_qual_names.size()) >= 2),
                "This is not multiple inheritance");
    // A hack to make it so we can reference clari exceptions before import clari is complete
    py::exec("def _subc(c):\n"
             "\ta = c.__subclasses__()\n"
             "\treturn a + [k for i in a for k in _subc(i)]\n"
             "_exs = {str(i).split(\"'\")[1]:i for i in _subc(Exception)}\n"
             // Error handling to make failures more comprehensible
             "def _ers(f):\n\ttry:\n\t\treturn f()\n\texcept KeyError as e:\n"
             "\t\traise Exception('Could not find designated base class: ' + str(e))\n");
    // Define shim class as subclasses of parents
    std::ostringstream gen;
    gen << "_ers(lambda: type('_EMIS',("; // _ers makes clean error messages
    for (auto &qual_name : pybind_qual_names) {
        gen << "_exs['" << API::root_mod_name << '.' << qual_name << "'],";
    }
    for (auto &name : native_names) {
        gen << name << ',';
    }
    gen << "),{}))";
    // Eval the constructed shim class, capture the PyObject *, make our exception subclass it
    return pybind11::register_exception<T>(m, ex_name, py::eval(gen.str()));
}

/** Translates a C++ exception to an existing python exception
 *  Note: this is a macro b/c this lambda must not capture to become a function pointer
 */
#define TRANSLATE_EXC(CPP_EXC, PY_EXC)                                                             \
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
/** A macro for brevity and consistency; provides a standard name */
#define REGISTER_INTERNAL_EXC(TYPE, BASE) py::register_exception<Util::Err::TYPE>(m, #TYPE, (BASE))
    // C++ exceptions; if python receives these, something went very wrong
    // Python functions do not need to plan for these, crashing should be ok
    // The base internal method, this is a fallback
    const auto internal { REGISTER_INTERNAL_EXC(Internal, claricpp) };
    // Collisions
    const auto collision { REGISTER_INTERNAL_EXC(Collision, internal) };
    REGISTER_INTERNAL_EXC(HashCollision, collision);
    // Directly derived classes
    // Note: some of these map to python builtin exception types
    // We choose not to map these to that, however, as these are internal claricpp exceptions
    // We thus choose to let them derive Internal instead.
    REGISTER_INTERNAL_EXC(Null, internal);
    REGISTER_INTERNAL_EXC(BadPath, internal);
    REGISTER_INTERNAL_EXC(Syscall, internal);
    REGISTER_INTERNAL_EXC(Size, internal);
    REGISTER_INTERNAL_EXC(Index, internal);
    REGISTER_INTERNAL_EXC(BadCast, internal);
    REGISTER_INTERNAL_EXC(BadVariantAccess, internal);
    REGISTER_INTERNAL_EXC(MissingVirtualFunction, internal);
    REGISTER_INTERNAL_EXC(Usage, internal);
    REGISTER_INTERNAL_EXC(RecurrenceLimit, internal);
    REGISTER_INTERNAL_EXC(Unknown, internal);
    REGISTER_INTERNAL_EXC(NotSupported, internal);
    REGISTER_INTERNAL_EXC(Type, internal);
}

/** Register generic python exceptions with pybind11 */
static void register_generic_python() {
    TRANSLATE_EXC(Util::Err::Python::Runtime, PyExc_RuntimeError); // prefer python builtin
}

/** Register claripy exceptions with pybind11 */
static void register_claripy(py::module_ &m, const py::handle &python) {
/** A macro for brevity and consistency; provides a standard name */
#define REGISTER_CLARIPY_EXC(NS, TYPE, BASE) py::register_exception<NS::TYPE>(m, #TYPE, BASE)
    // The base claripy exception; this is a fallback and useful for grouping, but should be unused
    const auto claripy { REGISTER_CLARIPY_EXC(Util::Err::Python, Claripy, python) };
    // Error::Backend
    namespace EBa = Error::Backend;
    REGISTER_CLARIPY_EXC(EBa, Abstraction, claripy);
    REGISTER_CLARIPY_EXC(EBa, Unsupported, claripy);
    // Error::Expr
    namespace EEx = Error::Expr;
    register_exception_mi<EEx::Value>(m, "Value", { "py_err.Claripy" }, { "ValueError" });
    register_exception_mi<EEx::Type>(m, "Type", { "py_err.Claripy" }, { "TypeError" });
    REGISTER_CLARIPY_EXC(EEx, Operation, claripy);
    REGISTER_CLARIPY_EXC(EEx, Usage, claripy);
    REGISTER_CLARIPY_EXC(EEx, Size, claripy);
}

/** Bind exceptions with pybind11 */
void API::bind_exceptions(py::module_ &root_module) {
    // Modules
    auto py_err { root_module.def_submodule("py_err", "python versions of claricpp errors") };
    auto internal { py_err.def_submodule("_internal", "Claricpp internal error python analogs") };
    // Base exceptions
    // Ideally, these should not be used; they are fallbacks and useful for grouping
    const auto base { py::register_exception<Util::Err::Claricpp>(internal, "Base") };
    const auto py_e { py::register_exception<Util::Err::Python::Base>(py_err, "BasePython", base) };
    // Derived and builtin derived exceptions
    // Note: Since we *cannot* do multiple inheritance due to a limitation in the python
    // C API and thus also in pybind11, we permit some types to map to python builtin exceptions
    // Ex., Util::Err::Python::Runtime, maps to a subclass of python's RuntimeError, nothing else
    // Note, however, that we do not require it if it makes more sense not to
    register_internal(internal, base);
    register_claripy(py_err, py_e);
    register_generic_python();
}