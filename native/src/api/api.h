/**
 * @file
 * @brief This header exposes the general C API functions for claricpp
 * \ingroup api
 */
#ifndef R_API_API_H_
#define R_API_API_H_

#include "constants.h"


/** A local macro used for consistency */
#define DECLARE_FREE_FUNC(TYPE, NAME)                                                              \
    /** Frees the internals of c_object and nulls out c_object                                     \
     *  @param c_object The object to be freed                                                     \
     */                                                                                            \
    void claricpp_free_##NAME(TYPE *const c_object);

/** A local macro used for consistency */
#define DECLARE_ARR_FREE_FUNC(TYPE, NAME)                                                          \
    /** Frees the objects in c_array, then frees c_array.arr and nulls c_array                     \
     *  @param c_array The array to have its contents and itself freed then nulled                 \
     */                                                                                            \
    void claricpp_free_array_##NAME(ARRAY_OUT(TYPE) *const c_array); // Yes, ARRAY_OUT

/** A local macro used for consistency */
#define DECLARE_DOUBLE_ARR_FREE_FUNC(TYPE, NAME)                                                   \
    /** Frees every array object, array, iteself, then nulls c_array                               \
     *  @param c_array The double array to have its contents and itself freed then nulled          \
     */                                                                                            \
    void claricpp_free_double_array_##NAME(DOUBLE_ARRAY_OUT(TYPE) *const c_array); // Yes, ARRAY_OUT

// Free functions

// Unions
DECLARE_FREE_FUNC(ClaricppPrim, prim);
DECLARE_FREE_FUNC(ClaricppArg, arg);

// Structs
DECLARE_FREE_FUNC(ClaricppAnnotation, annotation);
DECLARE_FREE_FUNC(ClaricppSPAV, spav);
DECLARE_FREE_FUNC(ClaricppExpr, expr);
DECLARE_FREE_FUNC(ClaricppBackend, backend);
DECLARE_FREE_FUNC(ClaricppSolver, solver);

// Arrays
DECLARE_ARR_FREE_FUNC(ClaricppAnnotation, annotation);
DECLARE_ARR_FREE_FUNC(ClaricppExpr, expr);
DECLARE_ARR_FREE_FUNC(ClaricppPrim, prim);
DECLARE_ARR_FREE_FUNC(ClaricppArg, arg);

// Double Arrays
DECLARE_DOUBLE_ARR_FREE_FUNC(ClaricppPrim, prim);

// Cleanup
#undef DECLARE_FREE_FUNC
#undef DECLARE_ARR_FREE_FUNC
#undef DECLARE_DOUBLE_ARR_FREE_FUNC

#endif