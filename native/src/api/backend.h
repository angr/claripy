/**
 * @file
 * @brief This header defines the C API for Backend
 * \ingroup api
*/
#ifndef R_BACKEND_H_
#define R_BACKEND_H_

#include "constants.h"


/********************************************************************/
/*                               Base                               */
/********************************************************************/

/** Get the name of the backend
 *  @return The name of the backend
 */
PyStr claricpp_backend_name(ClaricppBackend bk);

/** Use the backend to simplify expr
 *  @param bk The backend to use
 *  @param expr The Expr to simplify
 *  @return A bk simplified version of expr
 */
ClaricppExpr claricpp_backend_simplify(const ClaricppBackend bk, const ClaricppExpr expr);

/** Determine if bk supports expr
 *  @param bk The backend to use
 *  @param expr The Expr to check if bk supports
 *  @return true if and only if bk supports expr
 */
bool claricpp_backend_handles(const ClaricppBackend bk, const ClaricppExpr expr);

/** Clear some caches in order to reclaim excess memory
 *  @param bk The backend to reclaim memory from
 */
void claricpp_backend_downsize(const ClaricppBackend bk);

/** Clear persistent data caches
 *  These are caches that are not just for optimization.
 *  It is up to the user to ensure that this function is only called when safe to do so
 *  Warning: Do not use this function unless you understand what it does to the specific
 *  backend that has implemented it! It may clear vital persistent data from memory.
 *  @param bk The backend to reclaim memory from
 */
void claricpp_backend_clear_persistent_data(const ClaricppBackend bk);

/** Gets Backend's global BigInt mode
 *  @return The current BigInt mode
 */
ClaricppBIM claricpp_backend_get_big_int_mode();

/** Sets Backend's global BigInt mode
 *  @param m The BigInt mode to set the mode to
 *  @return The previous BigInt mode before it was updated
 */
ClaricppBIM claricpp_backend_set_big_int_mode(const ClaricppBIM m);

/********************************************************************/
/*                                Z3                                */
/********************************************************************/

#if 0
/** Set the BigInt abstraction mode for this backend */
inline Mode::BigInt big_int_mode(const Mode::BigInt m) noexcept {
    Util::Log::debug("Setting BitInt abstraction mode to ", m);
    return big_int_abstract_mode.exchange(m);
}

/** Get the BigInt abstraction mode for this backend */
inline Mode::BigInt big_int_mode() const noexcept { return big_int_abstract_mode; }
#endif


/********************************************************************/
/*                             Concrete                             */
/********************************************************************/

// @ todo

#endif
