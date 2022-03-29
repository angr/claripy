#include "manual.hpp"

#include "headers.hpp"

// For brevity
namespace py = pybind11;


/********************************************************************/
/*                      Exception Registration                      */
/********************************************************************/


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
#define REGISTER_INTERNAL_EXC(TYPE, BASE)                                                          \
    py::register_exception<Util::Err::TYPE>(m, "internal." #TYPE, (BASE))
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
static void register_generic_python(py::module_ &m, const py::handle &py_base) {
    TRANSLATE_EXC(Util::Err::Python::Runtime, PyExc_RuntimeError); // prefer python builtin
    (void) py_base;
    (void) m;
}

/** Register claripy exceptions with pybind11 */
static void register_claripy(py::module_ &m, const py::handle &python) {
/** A macro for brevity and consistency; provides a standard name */
#define REGISTER_CLARIPY_EXC(NS, TYPE, BASE)                                                       \
    py::register_exception<NS::TYPE>(m, "claripy." #TYPE "Error", BASE)
    // The base claripy exception; this is a fallback and useful for grouping, but should be unused
    const auto claripy { REGISTER_CLARIPY_EXC(Util::Err::Python, Claripy, python) };
    // Error::Backend
    namespace EBa = Error::Backend;
    REGISTER_CLARIPY_EXC(EBa, Abstraction, claripy);
    REGISTER_CLARIPY_EXC(EBa, Unsupported, claripy);
    // Error::Expr
    namespace EEx = Error::Expr;
    TRANSLATE_EXC(EEx::Value, PyExc_ValueError); // prefer python builtin
    TRANSLATE_EXC(EEx::Type, PyExc_TypeError);   // prefer python builtin
    REGISTER_CLARIPY_EXC(EEx, Operation, claripy);
    REGISTER_CLARIPY_EXC(EEx, Usage, claripy);
    REGISTER_CLARIPY_EXC(EEx, Size, claripy);
}

/** Register exceptions with pybind11 */
static void register_exceptions(py::module_ &m) {
    // Base exceptions
    // Ideally, these should not be used; they are fallbacks and useful for grouping
    const auto base { py::register_exception<Util::Err::Claricpp>(m, "BaseError") };
    const auto py_e { py::register_exception<Util::Err::Python::Base>(m, "PythonError", base) };
    // Derived and builtin derived exceptions
    // Note: Since we *cannot* do multiple inheritance due to a limitation in the python
    // C API and thus also in pybind11, we permit some types to map to python builtin exceptions
    // Ex., Util::Err::Python::Runtime, maps to a subclass of python's RuntimeError, nothing else
    // Note, however, that we do not require it if it makes more sense not to
    register_internal(m, base);
    register_generic_python(m, py_e);
    register_claripy(m, py_e);
}


/********************************************************************/
/*                           From Header                            */
/********************************************************************/


void API::bind_manual(py::module_ &m) {
    register_exceptions(m);
    // TODO: link logging systems (link classes and add + bind some init_logging() function)
    // TODO: hookup simplify (link classes and add + bind some init_simplify() function)
}