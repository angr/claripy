/**
 * @file
 * @brief This file contains macros used across claricpp
 */
#ifndef R_MACROS_HPP_
#define R_MACROS_HPP_


/** The CHAR_BIT claricpp will use */
#define C_CHAR_BIT 8

/** A macro that contains the information about the current line
 *  Useful for debugging
 */
#define WHOAMI __FILE__ ":", __LINE__, " (", __func__, "): "

/** A macro that contains the information about the current line
 *  Useful for debugging
 */
#define WHOAMI_WITH_SOURCE __FILE__ ": ", __LINE__, " (", __func__, ")  via " __BASE_FILE__ ": "


/** A macro to convert the value of a macro into a string */
#define MACRO_VALUE_TO_STRING(X) #X
/** A macro to convert a macro name into a string */
#define MACRO_TO_STRING(X) MACRO_VALUE_TO_STRING(X)

/** A macro to concat the two evaluated macros together */
#define MACRO_VALUE_CONCAT(A, B) A##B
/** A macro to concat the two macro evaluations */
#define MACRO_CONCAT(A, B) MACRO_VALUE_CONCAT(A, B)

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
#define LIKELY(X) __builtin_expect(!!(X), 1)

/** Hint to the compiler that x is unlikely; in C++20 use attributes
 *  In most cases, you should avoid this and use profile guided optimization
 */
#define UNLIKELY(X) __builtin_expect(!!(X), 0)


/********************************************************************/
/*          Define Subclasses That Use Parent Constructors          */
/********************************************************************/


/** A macro used to define a final derived subclass
 *  class which inherets its parent's constructors
 */
#define DEFINE_FINAL_SUBCLASS_USING_CTOR(DERIVED, SUPER)                                          \
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
#define SET_IMPLICITS_OPERATORS(CLASS, VALUE)                                                     \
    /** Define the copy operator */                                                               \
    CLASS &operator=(const CLASS &) = VALUE;                                                      \
    /** Define the move operator */                                                               \
    CLASS &operator=(CLASS &&) = VALUE;

/** A macro used to enable/disable the implicit non-default constructors of a class */
#define SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE)                                              \
    /** Define the default copy constructor */                                                    \
    CLASS(const CLASS &) = VALUE;                                                                 \
    /** Define the default move constructor */                                                    \
    CLASS(CLASS &&) = VALUE;

/** A macro used to enable/disable all implict constructors and operators of a class
 *  except for the default constructor
 */
#define SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CLASS, VALUE)                                          \
    SET_IMPLICITS_OPERATORS(CLASS, VALUE)                                                         \
    SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE)

/** A macro used to enable/disable all implicit constructors and operators of a class */
#define SET_IMPLICITS(CLASS, VALUE)                                                               \
    SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CLASS, VALUE)                                              \
    /** Define the default constructor */                                                         \
    CLASS() = VALUE;

/** Set the implicits of a class with const members */
#define SET_IMPLICITS_CONST_MEMBERS(CLASS, VALUE)                                                 \
    SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE)                                                  \
    SET_IMPLICITS_OPERATORS(CLASS, delete)                                                        \
    /** Disable the default constructor */                                                        \
    CLASS() = delete;


#endif
