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


/** A macro to convert the value of a macro into a string */
#define MACRO_VALUE_TO_STRING(X) #X

/** A macro to convert a macro name into a string */
#define MACRO_TO_STRING(X) MACRO_VALUE_TO_STRING(X)

#ifndef DEBUG
    /** Defined to noexcept when DEBUG is not defined */
    #define NOEXCEPT_UNLESS_DEBUG noexcept
#else
    // DEBUG defined case
    #define NOEXCEPT_UNLESS_DEBUG
#endif

/** Hint to the compiler that x is likely; in C++20 use attributes
 *  In most cases, you should avoid this and use profile guided optimization
 */
#define LIKELY(x) __builtin_expect(!!(x), 1)

/** Hint to the compiler that x is unlikely; in C++20 use attributes
 *  In most cases, you should avoid this and use profile guided optimization
 */
#define UNLIKELY(x) __builtin_expect(!!(x), 0)


/********************************************************************/
/*          Define Subclasses That Use Parent Constructors          */
/********************************************************************/


/** A macro used to define a final derived exception class
 *  This macro requires SUPER be in the same namespace
 */
#define DEFINE_FINAL_EXCEPTION(DERIVED, SUPER)                                                    \
    struct DERIVED final : public SUPER {                                                         \
        /** Inherit constructors */                                                               \
        using SUPER::SUPER;                                                                       \
    };

/** A macro used to define a non-final derived exception class
 *  This macro requires SUPER be in the same namespace
 *  Destructor is defaulted with noexcept
 */
#define DEFINE_NONFINAL_EXCEPTION(DERIVED, SUPER)                                                 \
    struct DERIVED : public SUPER {                                                               \
        SET_IMPLICITS_CONST_MEMBERS(DERIVED, default);                                            \
        /** Inherit constructors */                                                               \
        using SUPER::SUPER;                                                                       \
        /** Default virtual destructor */                                                         \
        inline virtual ~DERIVED() noexcept = default;                                             \
    };

/** A macro used to define a final derived exception class
 *  This macro does not require SUPER be in the same namespace
 */
#define DEFINE_NAMESPACED_FINAL_EXCEPTION(DERIVED, SUPER, NS)                                     \
    struct DERIVED final : public NS::SUPER {                                                     \
        /** Inherit constructors */                                                               \
        using NS::SUPER::SUPER;                                                                   \
    };


/********************************************************************/
/*                   Setters of implicit methods                    */
/********************************************************************/


/** A macro used to enable/disable the implict operators of a class */
#define SET_IMPLICITS_OPERATORS(CLASS, VALUE, ...)                                                \
    /** Define the copy operator */                                                               \
    CLASS &operator=(const CLASS &) __VA_ARGS__ = VALUE;                                          \
    /** Define the move operator */                                                               \
    CLASS &operator=(CLASS &&) __VA_ARGS__ = VALUE;

/** A macro used to enable/disable the implicit non-default constructors of a class */
#define SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE, ...)                                         \
    /** Define the default copy constructor */                                                    \
    CLASS(const CLASS &) __VA_ARGS__ = VALUE;                                                     \
    /** Define the default move constructor */                                                    \
    CLASS(CLASS &&) __VA_ARGS__ = VALUE;

/** A macro used to enable/disable all implict constructors and operators of a class
 *  except for the default constructor
 */
#define SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CLASS, VALUE, ...)                                     \
    SET_IMPLICITS_OPERATORS(CLASS, VALUE, __VA_ARGS__)                                            \
    SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE, __VA_ARGS__)

/** A macro used to enable/disable all implicit constructors and operators of a class */
#define SET_IMPLICITS(CLASS, VALUE, ...)                                                          \
    SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CLASS, VALUE, __VA_ARGS__)                                 \
    /** Define the default constructor */                                                         \
    CLASS() __VA_ARGS__ = VALUE;

/** Set the implicits of a class with const members */
#define SET_IMPLICITS_CONST_MEMBERS(CLASS, VALUE, ...)                                            \
    SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE, __VA_ARGS__)                                     \
    SET_IMPLICITS_OPERATORS(CLASS, delete)                                                        \
    /** Disable the default constructor */                                                        \
    CLASS() = delete;


#endif
