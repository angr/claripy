/**
 * @file
 * @brief This file defines the namespaces for documentation purposes
 * This file should not be included in any C++ code and will not compile intentionally
 */

/** A namespace that defines constants */
namespace Constants {}


/** A namespace used for the utils directory */
namespace Utils {

    /** A namespace that contains the max functions */
    namespace Max {}

    /** A namespace that contains private members of Utils
     *
     *  These members should not be called outside of the utils directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {}

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

        /** A namespace used to designate certain items in Utils::Log as private
         *
         *  These members should not be called outside of Utils::Log members
         */
        namespace Private {

            /** A namespace used to hold boolean which determine which logs are enabled */
            namespace Enabled {}

        } // namespace Private

        /** A namespace used for log styles */
        namespace Style {

            /** A namespace used for private members of style */
            namespace Private {}

        } // namespace Style

        /** A namespace used for log backends */
        namespace Backend {

            /** A namespace used for private members of backend */
            namespace Private {}

        } // namespace Backend

    } // namespace Log

} // namespace Utils


/** A namespace used for the ast directory */
namespace AST {

    /** A namespace used to designate certain items in ast as private
     *
     *  These members should not be called outside of the ast directory
     *  This is useful for helper functions templated functions call
     */
    namespace Private {}

    /** A namespace which contains the raw AST types that are factory constructed
     *
     *  These classes are unlikely to be accessed directly, but rather should be via an
     *  std::shared_ptr
     */
    namespace RawTypes {}

} // namespace AST


/** A namespace used for the errors directory */
namespace Errors {

    /** A namespace used for AST errors */
    namespace AST {}

    /** A namespace used exceptions to be passed back to python */
    namespace Python {}

    /** A namespace used for unexpected errors
     *
     *  These should never be thrown; they indicate an error with the code
     */
    namespace Unexpected {}

} // namespace Errors


/** A namespace used for the ops directory */
namespace Ops {

    /** These sets classify different Expression operations */
    namespace Expression {}

    /** These sets classify different Backend operations */
    namespace Backend {}

    /** These sets classify different Length operations */
    namespace Length {}

    /** These sets classify different Leaf operations */
    namespace Leaf {}

    /** These maps operations to related operations */
    namespace Maps {}

} // namespace Ops


/** A namespace used for the simplifications directory */
namespace Simplifications {

    /** A namespace used to designate certain items in Simplifications as private
     *
     *  These members should not be called outside of the simplifications directory
     */
    namespace Private {}

    /** A namespace which contains the simplifiers */
    namespace Simplifiers {

        /** A namespace for bv Simplifiers */
        namespace BV {}

        /** A namespace for shift Simplifiers */
        namespace Shift {}

        /** A namespace for boolean Simplifiers */
        namespace Boolean {}

        /** A namespace for bitwise Simplifiers */
        namespace Bitwise {}

    } // namespace Simplifiers

} // namespace Simplifications


/** A namespace used for the annotations directory */
namespace Annotation {}


/** A namespace used for unittesting instrumentation */
namespace UnitTest {}


/** Disable compilation */
#error This file exists only for documentation purposes
