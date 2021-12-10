/**
 * @file
 * @brief This header defines C constants to be used by the API
 * \ingroup api
 */
#ifndef R_API_CONSTANTS_H_
#define R_API_CONSTANTS_H_

#include <stddef.h>
#include <stdint.h>

/** Used to mark where the FFI parser should start from
 *  This struct is not used within the code base, instead
 *  it exists to tell the FFI parser to expose all methods
 *  which come after it after macro expansion
 */
struct ClaricppFFIStart;

// Copy enum generation macros
#include "../mode.h"


// Macros

/** Return the type of an input array of type T */
#define ARRAY_IN(T) const T *const

/** An array of X; can only be used by types that have corresponding array types */
#define ARRAY_OUT(X) X##OutArray

/** A forced eager evaluation of ARRAY_OUT */
#define EAGER_ARRAY_OUT(X) ARRAY_OUT(X)

/** An array of an array of X; can only be used by types that have double array types */
#define DOUBLE_ARRAY_OUT(X) EAGER_ARRAY_OUT(ARRAY_OUT(X))

/** A local macro used to declare a C wrapper for a C++ type */
#define DECLARE_WRAPPER(NAME)                                                                      \
    /** A C wrapper for a C++ type */                                                              \
    typedef struct {                                                                               \
        /** An obscure point to a C++ type */                                                      \
        void *ptr;                                                                                 \
    } NAME;

/** A local macro used to declare an out array of a C type */
#define DECLARE_OUT_ARRAY(NAME)                                                                    \
    /** The wrapper struct for the array */                                                        \
    typedef struct {                                                                               \
        /** An array of C objects */                                                               \
        NAME *arr;                                                                                 \
        /** The length of the array */                                                             \
        SIZE_T len;                                                                                \
    } ARRAY_OUT(NAME);

// Primitives

/** Define UINT as UInt without polluting the global namespace */
#define UINT unsigned long long
/** Define the unisigned type z3 uses */
#define Z3U unsigned
/** Define CUID_T as UInt without polluting the global namespace */
#define CUID_T UINT
/** Define SIZE_T as UInt without polluting the global namespace */
#define SIZE_T UINT
/** Define Hash::Hash without polluting the global namespace */
#define HASH_T unsigned long long
/** Define a type python can pass to represent a VS within claricpp */
#define VS_T unsigned long long

/** Define a boolean type */
#define BOOL int_fast8_t
/** C TRUE has a value of 1, like C++ true when cast to an int */
#define TRUE 1
/** C FALSE has a value of 0, like C++ false when cast to an int */
#define FALSE 0

// C Struct Types

DECLARE_WRAPPER(ClaricppAnnotation);
DECLARE_WRAPPER(ClaricppSPAV);
DECLARE_WRAPPER(ClaricppExpr);
DECLARE_WRAPPER(ClaricppBackend);
DECLARE_WRAPPER(ClaricppSolver);

// Other C types

/** The type a Python string argument is */
typedef ARRAY_IN(char) PyStr;

/** Claricpp rounding modes
 *  See mode/fp/rounding.h for more info
 */
typedef enum { MODE_FP_ROUNDING_VALS(ClaricppRm) } ClaricppRM;

/** Claricpp BigInt modes
 *  See mode/big_int.h for more info
 */
typedef enum { MODE_BIGINT_VALS(ClaricppBim) } ClaricppBIM;

/** Claricpp Width modes */
typedef enum { ClaricppWidthFloat, ClaricppWidthDouble } ClaricppWidth;

// Unions

/** A C union containing the primitive types an Expr can hold */
typedef union {
    // Literal types
    BOOL boolean;    // Bool
    const char *str; // String
    float flt;       // FP
    double dbl;      // FP
    uint64_t vs;     // VS
    // Literal BV types
    uint8_t u8;
    uint16_t u16;
    uint32_t u32;
    uint64_t u64;
    const char *big_int;
} ClaricppPrimUnion;

/** A C union containing the types an Expr can hold */
typedef union {
    ClaricppPrimUnion prim;
    ClaricppExpr expr;
    ClaricppRM rounding_mode;
    ClaricppWidth width;
} ClaricppArgUnion;

/** A C enum noting the types an Expr can hold */
typedef enum {
    ClaricppTypeEnumBool = 0,
    ClaricppTypeEnumStr,
    ClaricppTypeEnumFloat,
    ClaricppTypeEnumDouble,
    ClaricppTypeEnumVS,
    ClaricppTypeEnumU8,
    ClaricppTypeEnumU16,
    ClaricppTypeEnumU32,
    ClaricppTypeEnumU64,
    ClaricppTypeEnumBigInt,
    ClaricppTypeEnumExpr,
    ClaricppTypeEnumRM,
    ClaricppTypeEnumWidth
} ClaricppTypeEnum;

/** A safer C union containing the primitive types an Expr can hold */
typedef struct {
    /** The data this union holds */
    ClaricppPrimUnion data;
    /** The type of this data */
    ClaricppTypeEnum type;
} ClaricppPrim;

/** A safer C union containing the types an Expr can hold */
typedef struct {
    /** The data this union holds */
    ClaricppArgUnion data;
    /** The type of this data */
    ClaricppTypeEnum type;
} ClaricppArg;

// Array types

DECLARE_OUT_ARRAY(ClaricppAnnotation);
DECLARE_OUT_ARRAY(ClaricppExpr);
DECLARE_OUT_ARRAY(ClaricppPrim);
DECLARE_OUT_ARRAY(ARRAY_OUT(ClaricppPrim));
DECLARE_OUT_ARRAY(ClaricppArg);

// Cleanup
#undef DECLARE_OUT_ARRAY
#undef DECLARE_WRAPPER

// Exception

/** An enum of Claricpp exception types
 *  @todo: Make this support more
 */
typedef enum {
    ClaricppExceptionEnumNone = 0, // No exception
    ClaricppExceptionEnumUnknownCritical,
    ClaricppExceptionEnumUnknown,
    ClaricppExceptionEnumStd,
    ClaricppExceptionEnumUnexpected,
    ClaricppExceptionEnumPython
} ClaricppExceptionEnum;

/** The exception struct Claricpp sends to python */
typedef struct {
    /** The exception type */
    ClaricppExceptionEnum type;
    /** The exception message */
    const char *msg;
    /** The exception stack trace */
    const char *trace;
} ClaricppException;

#endif
