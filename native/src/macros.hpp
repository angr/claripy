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
#define WHOAMI_WITH_SOURCE __FILE__ " via " __BASE_FILE__ ": ", __LINE__, " (", __func__, "): "


/** A macro used to enable/disable the implict operators of a class */
#define SET_IMPLICITS_OPERATORS(CLASS, VALUE)                                                     \
    /** Disable copy operator */                                                                  \
    CLASS &operator=(const CLASS &) = VALUE;                                                      \
    /** Disable move operator */                                                                  \
    CLASS &operator=(CLASS &&) = VALUE;

/** A macro used to enable/disable the implicit non-default constructors of a class */
#define SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE)                                              \
    /** Disable default copy constructor */                                                       \
    CLASS(const CLASS &) = VALUE;                                                                 \
    /** Disable default move constructor */                                                       \
    CLASS(CLASS &&) = VALUE;

/** A macro used to enable/disable all implict constructors and operators of a class
 *  except for the default constructor
 */
#define SET_IMPLICITS_EXCLUDE_DEFAULT_CONSTRUCTOR(CLASS, VALUE)                                   \
    SET_IMPLICITS_OPERATORS(CLASS, VALUE)                                                         \
    SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE)

/** A macro used to enable/disable all implicit constructors and operators of a class */
#define SET_IMPLICITS(CLASS, VALUE)                                                               \
    SET_IMPLICITS_EXCLUDE_DEFAULT_CONSTRUCTOR(CLASS, VALUE)                                       \
    /** Disable default constructor */                                                            \
    CLASS() = VALUE;


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

/** A macro to convert the value of a macro into a string */
#define MACRO_VALUE_TO_STRING(X) #X

/** A macro to convert a macro name into a string */
#define MACRO_TO_STRING(X) MACRO_VALUE_TO_STRING(X)

#endif
