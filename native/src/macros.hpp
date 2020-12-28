/**
 * @file
 * @brief This file contains macros used across claricpp
 */
#ifndef __MACROS_HPP__
#define __MACROS_HPP__


/** A macro that contains the information about the current line
 *  Useful for debugging
 */
#define WHOAMI __FILE__ ":", __LINE__, " (", __func__, "): "

/** A macro that contains the information about the current line
 *  Useful for debugging
 */
#define WHOAMI_WITH_SOURCE                                                                        \
    __FILE_FILE__ " via " __BASE_FILE__ ": ", __LINE__, " (", __func__, "): "

/** A macro used to disable all default constructors of a class */
#define DELETE_DEFAULTS(X)                                                                        \
    /** Disable default constructor */                                                            \
    X() = delete;                                                                                 \
    /** Disable default copy constructor */                                                       \
    X(const X &) = delete;                                                                        \
    /** Disable default move constructor */                                                       \
    X(X &&) = delete;

/** A macro used to define a derived class that inherets its parent's constructors
 *  The body of this class is otherwise empty
 *  This macro requires SUPER be in the same namespace
 */
#define DEFINE_SUBCLASS_WITH_CONSTRUCTOR(DERIVED, SUPER)                                          \
    struct DERIVED : public SUPER {                                                               \
        /** Inherit constructors */                                                               \
        using SUPER::SUPER;                                                                       \
    };

/** A macro used to define a derived class that inherets its parent's constructors
 *  The body of this class is otherwise empty
 *  This macro does not require SUPER be in the same namespace
 */
#define DEFINE_NAMESPACED_SUBCLASS_WITH_CONSTRUCTOR(DERIVED, SUPER, NS)                           \
    struct DERIVED : public NS::SUPER {                                                           \
        /** Inherit constructors */                                                               \
        using NS::SUPER::SUPER;                                                                   \
    };

/** A macro to convert a macro result into a string */
#define MACRO_TO_STRING(X) MACRO_TO_STRING_HELPER(X)

/************************************************/
/*                   Helpers                    */
/************************************************/

/** A helper macro to help convert a macro result into a string */
#define MACRO_TO_STRING_HELPER(X) #X

#endif
