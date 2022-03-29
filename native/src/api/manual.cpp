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

/** Register unexpected Claricpp exceptions with pybind11 */
static void register_unexpected(py::module_ &m, const py::handle &claricpp) {
/** A macro for brevity and consistency; provides a standard name */
#define REGISTER_UNEXPECTED_SUB(TYPE, BASE)                                                        \
    py::register_exception<Util::Err::TYPE>(m, "internal." #TYPE, (BASE))
    // C++ exceptions; if python receives these, something went very wrong
    // Python functions do not need to plan for these, crashing should be ok
    // The base unexpected method, this is a fallback
    const auto unexpected { REGISTER_UNEXPECTED_SUB(Unexpected, claricpp) };
    // Collisions
    const auto collision { REGISTER_UNEXPECTED_SUB(Collision, unexpected) };
    REGISTER_UNEXPECTED_SUB(HashCollision, collision);
    // Directly derived classes
    // Note: some of these map to python builtin exception types
    // We choose not to map these to that, however, as these are internal claricpp exceptions
    // We thus choose to let them derive Unexpected instead.
    REGISTER_UNEXPECTED_SUB(Null, unexpected);
    REGISTER_UNEXPECTED_SUB(BadPath, unexpected);
    REGISTER_UNEXPECTED_SUB(Syscall, unexpected);
    REGISTER_UNEXPECTED_SUB(Size, unexpected);
    REGISTER_UNEXPECTED_SUB(Index, unexpected);
    REGISTER_UNEXPECTED_SUB(BadCast, unexpected);
    REGISTER_UNEXPECTED_SUB(BadVariantAccess, unexpected);
    REGISTER_UNEXPECTED_SUB(MissingVirtualFunction, unexpected);
    REGISTER_UNEXPECTED_SUB(Usage, unexpected);
    REGISTER_UNEXPECTED_SUB(RecurrenceLimit, unexpected);
    REGISTER_UNEXPECTED_SUB(Unknown, unexpected);
    REGISTER_UNEXPECTED_SUB(NotSupported, unexpected);
    REGISTER_UNEXPECTED_SUB(Type, unexpected);
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
#define REGISTER_CLARIPY_SUB(NS, TYPE, BASE)                                                       \
    py::register_exception<NS::TYPE>(m, "claripy." #TYPE "Error", BASE)
    // The base claripy exception; this is a fallback and useful for grouping, but should be unused
    const auto claripy { REGISTER_CLARIPY_SUB(Util::Err::Python, Claripy, python) };
    // Error::Backend
    namespace EBa = Error::Backend;
    REGISTER_CLARIPY_SUB(EBa, Abstraction, claripy);
    REGISTER_CLARIPY_SUB(EBa, Unsupported, claripy);
    // Error::Expr
    namespace EEx = Error::Expr;
    TRANSLATE_EXC(EEx::Value, PyExc_ValueError); // prefer python builtin
    TRANSLATE_EXC(EEx::Type, PyExc_TypeError);   // prefer python builtin
    REGISTER_CLARIPY_SUB(EEx, Operation, claripy);
    REGISTER_CLARIPY_SUB(EEx, Usage, claripy);
    REGISTER_CLARIPY_SUB(EEx, Size, claripy);
}

/** Register exceptions with pybind11 */
static void register_exceptions(py::module_ &m) {
    namespace UE = Util::Err;
    namespace UEP = UE::Python;
    // Base exceptions
    // Ideally, these should not be used; they are fallbacks and useful for grouping
    const auto claricpp { py::register_exception<UE::Claricpp>(m, "BaseError") };
    const auto python { py::register_exception<UEP::Base>(m, "PythonError", claricpp) };
    // Derived and builtin derived exceptions
    // Note: Since we *cannot* do multiple inheritance due to a limitation in the python
    // C API and thus also in pybind11, we permit some types to map to python builtin exceptions
    // Ex., Util::Err::Python::Runtime, maps to a subclass of python's RuntimeError, nothing else
    // Note, however, that we do not require it if it makes more sense not to
    register_unexpected(m, claricpp);
    register_generic_python(m, python);
    register_claripy(m, python);
}


/********************************************************************/
/*                           From Header                            */
/********************************************************************/


void API::bind_manual(py::module_ &m) {
    register_exceptions(m);
}