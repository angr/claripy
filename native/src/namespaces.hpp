/**
 * @file
 * @brief This file defines the namespaces for documentation purposes
 * This file should not be included in any C++ code and will not compile intentionally
 */

/** A namespace that defines constants */
namespace Constants {}


/** A namespace used for the util directory */
namespace Util {

    /** A namespace that contains the max functions */
    namespace Max {}

    /** A namespace that contains members used to ensure thread safety */
    namespace ThreadSafe {}

    /** A namespace that contains private members of Util
     *
     *  These members should not be called outside of the util directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {}

    /** A namespace used to contain color terminal codes */
    namespace ANSIColorCodes {

        /** Bold color codes */
        namespace Bold {}
        /** Underlined color codes */
        namespace Underline {}
        /** High intensity color codes */
        namespace HighIntensity {
            /** HighIntensity Bold */
            namespace Bold {}
        } // namespace HighIntensity
        /** Background color codes */
        namespace Background {
            /** High intensity background color codes */
            namespace HighIntensity {}
        } // namespace Background

    } // namespace ANSIColorCodes

    /** A namespace used for the util's error directory */
    namespace Error {

        /** A namespace used exceptions to be passed back to python */
        namespace Python {}

    } // namespace Error

    /** A namespace used for logging functions
     *
     *  Unless otherwise specified, each public logging function in this namespace takes in
     *  whatever arguments it is given by copy, and returns void. There are no restrictions on
     *  what types of arguments, or how many arguments are given, other than that the '<<'
     *  stream operator must be defined for the type. Optionally, a class can be provided as an
     *  extra template argument to log. If it is provided the log written to will be a custom log
     *  related to that particular class. If no custom log is specified a default log is used.
     */
    namespace Log {

        /** A namespace used to designate certain items in Util::Log as private
         *
         *  These members should not be called outside of Util::Log members
         */
        namespace Private {}

        /** A namespace used for log level members */
        namespace Level {}

        /** A namespace used for log styles */
        namespace Style {

            /** A namespace used for private members of Style */
            namespace Private {}

        } // namespace Style

        /** A namespace used for log backends */
        namespace Backend {

            /** A namespace used for private members of Backend */
            namespace Private {}

        } // namespace Backend

    } // namespace Log

    /** A namespace used for members related to bit masks */
    namespace BitMask {

        /** A namespace used for private members of BitMask */
        namespace Private {}

    } // namespace BitMask

    /** A namespace used for stack limit related members */
    namespace StackLimit {}

    /** A namespace used for type dependent constants */
    namespace TD {}

    /** A namespace used for constant dependent constants */
    namespace CD {}

} // namespace Util

/** A namespace used for the CUID related members */
namespace CUID {}

/** A namespace used for the factory directory */
namespace Factory {

    /** A namespace used for private members of factory */
    namespace Private {}

} // namespace Factory

/** A namespace used for the hash directory */
namespace Hash {}

/** A namespace used for the mode directory */
namespace Mode {}

/** A namespace used for the error directory */
namespace Error {

    /** A namespace used for Expr errors */
    namespace Expr {}

    /** A namespace used for Backend errors */
    namespace Backend {}

} // namespace Error

/** A namespace used for the expr directory */
namespace Expr {}

/** a namespace used for the backend directory */
namespace Backend {

    /** A namespace used for the z3 backend */
    namespace Z3 {

        /** A namespace used for z3::expr->Expr abstraction functions */
        namespace Abstract {}

        /** A namespace used for Expr->z3::expr conversion functions */
        namespace Convert {

            /** A namespace used for String specific Expr->z3::expr conversion functions */
            namespace String {}

            /** A namespace used for private members of Backend::Z3::Convert */
            namespace Private {}

            /** A namespace used for FP specific Expr->z3::expr conversion functions */
            namespace FP {

                /** A namespace used for private members of Backend::Z3::Convert::FP */
                namespace Private {}

            } // namespace FP
        }     // namespace Convert

        /** A namespace used for FP width related objects */
        namespace FP {}

        /** A namespace used for private members of Backend::Z3 */
        namespace Private {}

    } // namespace Z3

} // namespace Backend

/** A namespace that contains the various Op classes */
namespace Op {

    /** A namespace that contains various FP Op classes */
    namespace FP {}

    /** A namespace that contains various String Op classes */
    namespace String {}

} // namespace Op

/** A namespace used for the py_obj directory */
namespace PyObj {}

/** A namespace that contains various C API functions */
namespace C_API {

    /** A namespace that contains private members of the C API */
    namespace Private {}

} // namespace C_API

/** A namespace used for the simplification directory */
namespace Simplification {

    /** A namespace which contains the simplifiers */
    namespace Simplifier {

        /** A namespace for bv Simplifiers */
        namespace BV {}
        /** A namespace for shift Simplifiers */
        namespace Shift {}
        /** A namespace for boolean Simplifiers */
        namespace Boolean {}
        /** A namespace for bitwise Simplifiers */
        namespace Bitwise {}

    } // namespace Simplifier

} // namespace Simplification

/** A namespace used for members which create exprs with ops
 *
 *  These are analogous to functions like __add__ in claripy; they create
 *  an op via a factory, then create an expr with said op
 */
namespace Create {

    /** A namespace for FP creation functions */
    namespace FP {}

    /** A namespace for String creation functions */
    namespace String {

        /** A namespace for private members of Create::String */
        namespace Private {}

    } // namespace String

    /** A namespace for private members of Create */
    namespace Private {}

} // namespace Create

/** A namespace used for the annotations directory */
namespace Annotation {}


/** A namespace used for unit testing instrumentation */
namespace UnitTest {}


/** Disable compilation */
#error This file exists only for documentation purposes
