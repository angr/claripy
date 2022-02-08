/**
 * @file
 * @brief This header defines general aspects of the API
 * \ingroup api
 */
#ifndef R_API_GENERAL_H_
#define R_API_GENERAL_H_

#include "constants.h"


/********************************************************************/
/*                            Callbacks                             */
/********************************************************************/


/** The log callback type */
typedef void (*const ClaricppPyLog)(PyStr, const ClaricppLogLvl, PyStr);

/** The level getter callback type */
typedef ClaricppLogLvl (*const ClaricppPyLevel)(PyStr);

/** The python simplification callback */
typedef ClaricppExpr (*ClaricppSimp)(const ClaricppExpr);

/********************************************************************/
/*                             General                              */
/********************************************************************/


/** Configures claricpp to be used by python
 *  This does things like change the logging backend
 *  @param src The src directory of claricpp (used by backward for file info); ignored if null
 *  @param py_log The python logging callback the logging system should use
 *  @param py_lvl The python log level getter callback the logging system should use
 *  @param py_simp The claricpp python simplifier callback (may be null)
 */
void claricpp_init_for_python_usage(PyStr src, ClaricppPyLog py_log, ClaricppPyLevel py_lvl, ClaricppSimp py_simp);

/** Returns true if and only if the previous API function failed with an exception
 *  This function will not override the saved exception, on failure the program will crash
 *  @return true if and only if the previous API function failed with an exception
 */
BOOL claricpp_has_exception();

/** Returns the C++ exception Claricpp threw during the previous API function call
 *  This function should only be called if claricpp_has_exception() is true
 *  If this function fails, the failure exception is returned but the saved exception is not cleared
 *  @return The C++ exception Claricpp threw during the previous API function call
 */
ClaricppException claricpp_get_exception();


/********************************************************************/
/*                          Free Functions                          */
/********************************************************************/


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

/** Free a claricpp exception
 *  Tis function will not raise an exception
 */
void claricpp_free_exception(ClaricppException e);

#endif
