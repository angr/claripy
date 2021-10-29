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
const char * claricpp_backend_name(ClaricppBackend bk);

/** Determine if bk supports expr
 *  @param bk The backend to use
 *  @param expr The Expr to check if bk supports
 *  @return true if and only if bk supports expr
 */
bool claricpp_backend_handles(const ClaricppBackend bk, const ClaricppExpr expr);

/** Use the backend to simplify expr
 *  @param bk The backend to use
 *  @param expr The Expr to simplify
 *  @return A bk simplified version of expr
 */
ClaricppExpr claricpp_backend_simplify(const ClaricppBackend bk, const ClaricppExpr expr);

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

/** Create a Z3 backend
 *  @return A new Z3 backend
 */
ClaricppBackend claricpp_backend_z3_new();

ClaricppSolver claricpp_backend_z3_tls_solver(const ClaricppBackend z3, const Z3U timeout);

ClaricppSolver claricpp_backend_z3_new_tls_solver(const ClaricppBackend z3, const Z3U timeout);

#if 0
void claricpp_backend_z3_add_tracked(const ClaricppSolver, const ClaricppExpr constraint);

void claricpp_backend_z3_add_vec_tracked(const ClaricppSolver, const ClaricppExpr constraint); // todo

void claricpp_backend_z3_add_vec_untracked(const ClaricppSolver, const ClaricppExpr constraint); // todo

void claricpp_backend_z3_add_untracked(const ClaricppSolver, const ClaricppExpr constraint);

bool claricpp_backend_z3_satisfiable(const ClaricppSolver, const ClaricppExpr constraint);

bool claricpp_backend_z3_satisfiable_ec(const ClaricppSolver, const ClaricppExpr constraint); // todo
#endif

#if 0
inline bool solution(const Expr::RawPtr expr, const Expr::RawPtr sol, z3::solver &solver,
                     const std::vector<Expr::RawPtr> &extra_constraints) {}

inline bool solution(const Expr::RawPtr expr, const Expr::RawPtr sol, z3::solver &solver) {}

template <bool Signed> inline auto min(const Expr::RawPtr expr, z3::solver &solver) {}

template <bool Signed>
inline auto min(const Expr::RawPtr expr, z3::solver &solver,
                const std::vector<Expr::RawPtr> &extra_constraints) {}

template <bool Signed> inline auto max(const Expr::RawPtr expr, z3::solver &solver) {}

template <bool Signed>
inline auto max(const Expr::RawPtr expr, z3::solver &solver,
                const std::vector<Expr::RawPtr> &extra_constraints) {}

inline std::vector<Expr::BasePtr> unsat_core(z3::solver &solver) {}

inline std::vector<PrimVar> eval(const Expr::RawPtr expr, z3::solver &solver,
                                 const UInt n_sol)

inline std::vector<PrimVar> eval(const Expr::RawPtr expr, z3::solver &s, const UInt n,
                                 const std::vector<Expr::RawPtr> &extra_constraints)

inline std::vector<std::vector<PrimVar>> batch_eval(const std::vector<Expr::RawPtr> &exprs,
                                                    z3::solver &s, const UInt n)

inline std::vector<std::vector<PrimVar>>
batch_eval(const std::vector<Expr::RawPtr> &exprs, z3::solver &s, const UInt n,
           const std::vector<Expr::RawPtr> &extra_constraints)
#endif


/********************************************************************/
/*                             Concrete                             */
/********************************************************************/

// @ todo

#endif
