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


/** Used to declare a C wrapper for a C++ type */
#define DECLARE_WRAPPER(NAME) \
    /** A C wrapper for a C++ type */ \
    struct NAME { void * ptr; }

DECLARE_WRAPPER(ClaricppAnnotation);
DECLARE_WRAPPER(ClaricppSPAV);
DECLARE_WRAPPER(ClaricppExpr);
DECLARE_WRAPPER(ClaricppBackend);

/** Return the type of an input array of type T */
#define ARRAY_IN(T) const T * const

/** The type a Python string argument is */
typedef ARRAY_IN(char) PyStr;

/** Define UINT as UInt without polluting the global namespace */
#define UINT unsigned long long
/** Define SIZE_T as UInt without polluting the global namespace */
#define SIZE_T unsigned long long
/** Define Hash::Hash without polluting the global namespace */
#define HASH_T unsigned long long
/** Define a type python can pass to represent a VS within claricpp */
#define VS_T unsigned long long

/** Claricpp rounding modes
 *  See mode/fp/rounding.h for more info
 */
enum ClaricppRM { MODE_FP_ROUNDING_VALS(ClaricppRm) };

/** Claricpp BigInt modes
 *  See mode/big_int.h for more info
 */
enum ClaricppBIM { MODE_BIGINT_VALS(ClaricppBim) };

// Cleanup
#undef DECLARE_WRAPPER

#endif
