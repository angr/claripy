/**
 * @file
 * @brief This file contains macros used across claricpp
 */
#ifndef R_SRC_MACROS_HPP_
#define R_SRC_MACROS_HPP_


/** A macro that contains the information about the current line
 *  Useful for debugging
 */
#define WHOAMI_HEADER_ONLY __FILE__ ":", __LINE__, " (", __func__, "): "

/** A macro that contains the information about the current line
 *  Useful for debugging
 */
#define WHOAMI __FILE__ ": ", __LINE__, " (", __func__, ") via " __BASE_FILE__ ": "


/** A macro to convert the value of a macro into a string */
#define MACRO_VALUE_TO_STRING(X) #X
/** A macro to convert a macro name into a string */
#define MACRO_TO_STRING(X) MACRO_VALUE_TO_STRING(X)

/** A macro to concat the two evaluated macros together */
#define MACRO_VALUE_CONCAT(A, B) A##B
/** A macro to concat the two macro evaluations */
#define MACRO_CONCAT(A, B) MACRO_VALUE_CONCAT(A, B)


#ifdef DEBUG
    /** Defined to noexcept when DEBUG is not defined */
    #define NOEXCEPT_UNLESS_DEBUG
    /** True is DEBUG else false */
    #define TRUE_IF_DEBUG true
#else
    #define NOEXCEPT_UNLESS_DEBUG noexcept
    #define TRUE_IF_DEBUG false
#endif

#ifdef DEBUG
    /** Define a macro used to help with debugging */
    #define HERE(LOG) Util::Log::LOG(WHOAMI);
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
/*                   Setters of implicit methods                    */
/********************************************************************/


/** A macro used to enable/disable the implicit operators of a class
 *  noexcept may be added as a third optional argument applied to move semantics
 */
#define SET_IMPLICITS_OPERATORS(CLASS, VALUE, ...)                                                 \
    /** Define the copy operator */                                                                \
    CLASS &operator=(const CLASS &) = VALUE;                                                       \
    /** Define the move operator */                                                                \
    CLASS &operator=(CLASS &&) __VA_ARGS__ = VALUE;

/** A macro used to enable/disable the implicit non-default constructors of a class
 *  noexcept may be added as a third optional argument applied to move semantics
 */
#define SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE, ...)                                          \
    /** Define the default copy constructor */                                                     \
    CLASS(const CLASS &) = VALUE;                                                                  \
    /** Define the default move constructor */                                                     \
    CLASS(CLASS &&) __VA_ARGS__ = VALUE;

/** A macro used to enable/disable all implicit constructors and operators of a class
 *  except for the default constructor
 *  noexcept may be added as a third optional argument applied to move semantics
 */
#define SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CLASS, VALUE, ...)                                      \
    SET_IMPLICITS_OPERATORS(CLASS, VALUE, __VA_ARGS__)                                             \
    SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE, __VA_ARGS__)

/** A macro used to enable/disable all implicit constructors and operators of a class
 *  noexcept may be added as a third optional argument applied to move semantics
 */
#define SET_IMPLICITS(CLASS, VALUE, ...)                                                           \
    SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(CLASS, VALUE, __VA_ARGS__)                                  \
    /** Define the default constructor */                                                          \
    CLASS() = VALUE;

/** Set the implicits of a class with const members
 *  noexcept may be added as a third optional argument applied to move semantics
 */
#define SET_IMPLICITS_CONST_MEMBERS(CLASS, VALUE, ...)                                             \
    SET_IMPLICITS_NONDEFAULT_CTORS(CLASS, VALUE, __VA_ARGS__)                                      \
    SET_IMPLICITS_OPERATORS(CLASS, delete)                                                         \
    /** Disable the default constructor */                                                         \
    CLASS() = delete;

// All noexcept implicits

/** A macro used to enable the implicit operators of a class as noexcept */
#define DEFINE_IMPLICITS_OPERATORS_ALL_NOEXCEPT(CLASS)                                             \
    /** Define the copy operator */                                                                \
    CLASS &operator=(const CLASS &) noexcept = default;                                            \
    /** Define the move operator */                                                                \
    CLASS &operator=(CLASS &&) noexcept = default;

/** A macro used to enable the implicit non-default constructors of a class as noexcept */
#define DEFINE_IMPLICITS_NONDEFAULT_CTORS_ALL_NOEXCEPT(CLASS)                                      \
    /** Define the default copy constructor */                                                     \
    CLASS(const CLASS &) noexcept = default;                                                       \
    /** Define the default move constructor */                                                     \
    CLASS(CLASS &&) noexcept = default;

/** A macro used to enable all implicit constructors and operators of a class as noexcept
 *  except for the default constructor which is not set at all
 */
#define DEFINE_IMPLICITS_EXCLUDE_DEFAULT_CTOR_ALL_NOEXCEPT(CLASS)                                  \
    DEFINE_IMPLICITS_OPERATORS_ALL_NOEXCEPT(CLASS)                                                 \
    DEFINE_IMPLICITS_NONDEFAULT_CTORS_ALL_NOEXCEPT(CLASS)

/** A macro used to enable all implicit constructors and operators of a class as noexcept */
#define DEFINE_IMPLICITS_ALL_NOEXCEPT(CLASS)                                                       \
    DEFINE_IMPLICITS_EXCLUDE_DEFAULT_CTOR_ALL_NOEXCEPT(CLASS)                                      \
    /** Define the default constructor */                                                          \
    CLASS() noexcept = default;

/** Set the implicits of a class with const members as noexcept */
#define DEFINE_IMPLICITS_CONST_MEMBERS_ALL_NOEXCEPT(CLASS)                                         \
    DEFINE_IMPLICITS_NONDEFAULT_CTORS_ALL_NOEXCEPT(CLASS)                                          \
    SET_IMPLICITS_OPERATORS(CLASS, delete)                                                         \
    /** Disable the default constructor */                                                         \
    CLASS() = delete;


#endif
