/**
 * @file
 * @brief This header defines C constants to be used by the API
 * \ingroup api
 */
#ifndef R_API_CONSTANTS_H_
#define R_API_CONSTANTS_H_

#include <stddef.h>
#include <stdint.h>

// Copy enum generation macros
#include "../mode.h"


// Macros

/** Return the type of an input array of type T */
#define ARRAY_IN(T) const T *const

/** An array of X; can only be used by types that have corresponding array types */
#define ARRAY_OUT(X) X##OutArray

/** A local macro used to declare a C wrapper for a C++ type */
#define DECLARE_WRAPPER(NAME)                                                                      \
    /** A C wrapper for a C++ type */                                                              \
    struct NAME {                                                                                  \
        /** An obscure point to a C++ type */                                                      \
        void *ptr;                                                                                 \
    }

/** A local macro used to declare an out array of a C type */
#define DECLARE_OUT_ARRAY(NAME)                                                                    \
    /** The wrapper struct for the array */                                                        \
    struct ARRAY_OUT(NAME) {                                                                       \
        /** An array of C objects */                                                               \
        struct NAME *arr;                                                                          \
        /** The length of the array */                                                             \
        SIZE_T len;                                                                                \
    }

// Primitives

/** Define UINT as UInt without polluting the global namespace */
#define UINT unsigned long long
/** Define the unisigned type z3 uses */
#define Z3U unsigned
/** Define SIZE_T as UInt without polluting the global namespace */
#define SIZE_T unsigned long long
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

DECLARE_OUT_ARRAY(ClaricppExpr);

// Cleanup
#undef DECLARE_WRAPPER
#undef DECLARE_OUT_ARRAY

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
union ClaricppPrimUnion {
    // Literal types
    BOOL boolean; // Bool
    PyStr str;    // String
    float flt;    // FP
    double dbl;   // FP
    uint64_t vs;  // VS  @todo
    // Literal BV types
    uint8_t u8;
    uint16_t u16;
    uint32_t u32;
    uint64_t u64;
    PyStr big_int;
};

/** A C union containing the types an Expr can hold */
union ClaricppArgUnion {
    union ClaricppPrimUnion prim;
    struct ClaricppExpr expr;
    ClaricppRM rounding_mode;
    ClaricppWidth width; // @todo
};

/** A local macro used for consistency */
#define PRIM_ENUM(NAME)                                                                            \
    Claricpp##NAME##Bool = 0, Claricpp##NAME##Str, Claricpp##NAME##Float, Claricpp##NAME##Double,  \
    Claricpp##NAME##VS, Claricpp##NAME##U8, Claricpp##NAME##U16, Claricpp##NAME##U32,              \
    Claricpp##NAME##U64, Claricpp##NAME##BigInt

/** A C enum noting the primitive types an Expr can hold */
enum ClaricppPrimEnum { PRIM_ENUM(PrimEnum) }; // @ todo

/** A C enum noting the types an Expr can hold */
enum ClaricppArgEnum {
    PRIM_ENUM(ArgEnum),
    ClaricppArgEnumExpr,
    ClaricppArgEnumRM,
    ClaricppArgEnumWidth
}; // @ todo

// Cleanup
#undef PRIM_ENUM

/** A safer C union containing the primitive types an Expr can hold */
struct ClaricppPrim {
    /** The data this union holds */
    union ClaricppPrimUnion data;
    /** The type of this data */
    enum ClaricppPrimEnum type;
};

/** A safer C union containing the types an Expr can hold */
struct ClaricppArg {
    /** The data this union holds */
    union ClaricppArgUnion data;
    /** The type of this data */
    enum ClaricppArgEnum type;
};


#endif
