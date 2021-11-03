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
const char *claricpp_backend_name(ClaricppBackend bk);

/** Determine if bk supports expr
 *  @param bk The backend to use
 *  @param expr The Expr to check if bk supports
 *  @return true if and only if bk supports expr
 */
BOOL claricpp_backend_handles(const ClaricppBackend bk, const ClaricppExpr expr);

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

/** Get a solver from the Z3 backend that should never be shared between threads
 *  @param z3 The Z3 backend to use
 *  @param timeout A timeout to apply to the got solver, even if the solver is being reused
 *  @return A solver of the Z3 backend that should never be shared between threads
 */
ClaricppSolver claricpp_backend_z3_tls_solver(const ClaricppBackend z3, const Z3U timeout);

/** Get a new solver from the Z3 backend that should never be shared between threads
 *  Note: This solver will not be reused by the Z3 backend anywhere
 *  @param z3 The Z3 backend to use
 *  @param timeout A timeout to apply to the new solver
 *  @return A new, not internally saved, solver that should never be shared between threads
 */
ClaricppSolver claricpp_backend_z3_new_tls_solver(const ClaricppBackend z3, const Z3U timeout);

/** Add a constraint to the solver and track it
 *  @param z3 The Z3 backend to use
 *  @param solver The solver to be added to
 *  @param constraint The constraint to add to solver
 */
void claricpp_backend_z3_add_tracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                     const ClaricppExpr constraint);

/** Add an array of constraints to the solver and track them
 *  @param z3 The Z3 backend to use
 *  @param solver The solver to be added to
 *  @param constraints The array of constraints to add to solver and track
 *  @param len The length of constraints
 */
void claricpp_backend_z3_add_vec_tracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                         ARRAY_IN(ClaricppExpr) constraints, const SIZE_T len);

/** Add a constraint to the solver
 *  @param z3 The Z3 backend to use
 *  @param solver The solver to be added to
 *  @param constraint The constraint to add to solver
 */
void claricpp_backend_z3_add_untracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                       const ClaricppExpr constraint);

/** Add an array of constraints to the solver
 *  @param z3 The Z3 backend to use
 *  @param solver The solver to be added to
 *  @param constraints The array of constraints to add to solver
 *  @param len The length of constraints
 */
void claricpp_backend_z3_add_vec_untracked(const ClaricppBackend z3, const ClaricppSolver solver,
                                           ARRAY_IN(ClaricppExpr) constraints, const SIZE_T len);

/** Determine if a solver is satisfiable
 *  @param z3 The Z3 backend to use
 *  @param solver The solver to check the satisfiability of
 *  @return True if solver is satisfiable
 */
BOOL claricpp_backend_z3_satisfiable(const ClaricppBackend z3, const ClaricppSolver solver);

/** Determine if a solver is satisfiable given extra constraints
 *  @param z3 The Z3 backend to use
 *  @param solver The solver to check the satisfiability of
 *  @param extra_constraints An array of extra constraints required be simultaneously satisfiable
 *  @param len The length of the extra_constraints array
 *  @return True if and only if solver and extra_constraints are simultaneously satisfiable
 */
BOOL claricpp_backend_z3_satisfiable_ec(const ClaricppBackend z3, const ClaricppSolver solver,
                                        ARRAY_IN(ClaricppExpr) extra_constraints, const SIZE_T len);

/** Determine if an expression is a solution to the given solver
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to which we are providing a solution for
 *  @param sol The solution we are providing for expr
 *  @param solver The solver the solution must satisfy
 *  @return True if and only if solver is satisfiable given the extra constraint (expr == sol)
 */
BOOL claricpp_backend_z3_solution(const ClaricppBackend z3, const ClaricppExpr expr,
                                  const ClaricppExpr sol, const ClaricppSolver solver);

/** Determine if an expression is a solution to the given solver given extra constraints
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to which we are providing a solution for
 *  @param sol The solution we are providing for expr
 *  @param solver The solver the solution must satisfy
 *  @param extra_constraints An array of extra constraints required be simultaneously satisfiable
 *  @param len The length of the extra_constraints array
 *  @return True if and only if solver and extra_constraints are satisfiable given (expr == sol)
 */
BOOL claricpp_backend_z3_solution_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                     const ClaricppExpr sol, const ClaricppSolver solver,
                                     ARRAY_IN(ClaricppExpr) extra_constraints, const SIZE_T len);

/** Minimize a signed z3 expr subjects to the constraints of a solver
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to minimize
 *  @param solver The solver whose constraints expr must be subject to
 *  @return The value of expr when it is minimized subject to the solver
 */
int64_t claricpp_backend_z3_min_signed(const ClaricppBackend z3, const ClaricppExpr expr,
                                       const ClaricppSolver solver);

/** Minimize a signed z3 expr subjects to the constraints of a solver and extra constraints
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to minimize
 *  @param solver The solver whose constraints expr must be subject to
 *  @param extra_constraints An array of extra constraints required be simultaneously satisfiable
 *  @param len The length of the extra_constraints array
 *  @return The value of expr when it is minimized subject to the solver and extra constraints
 */
int64_t claricpp_backend_z3_min_signed_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                          const ClaricppSolver solver,
                                          ARRAY_IN(ClaricppExpr) extra_constraints,
                                          const SIZE_T len);

/** Minimize a unsigned z3 expr subjects to the constraints of a solver
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to minimize
 *  @param solver The solver whose constraints expr must be subject to
 *  @return The value of expr when it is minimized subject to the solver
 */
uint64_t claricpp_backend_z3_min_unsigned(const ClaricppBackend z3, const ClaricppExpr expr,
                                          const ClaricppSolver solver);

/** Minimize a unsigned z3 expr subjects to the constraints of a solver and extra constraints
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to minimize
 *  @param solver The solver whose constraints expr must be subject to
 *  @param extra_constraints An array of extra constraints required be simultaneously satisfiable
 *  @param len The length of the extra_constraints array
 *  @return The value of expr when it is minimized subject to the solver and extra constraints
 */
uint64_t claricpp_backend_z3_min_unsigned_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                             const ClaricppSolver solver,
                                             ARRAY_IN(ClaricppExpr) extra_constraints,
                                             const SIZE_T len);


/** Maximize a signed z3 expr subjects to the constraints of a solver
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to maximize
 *  @param solver The solver whose constraints expr must be subject to
 *  @return The value of expr when it is maximized subject to the solver
 */
int64_t claricpp_backend_z3_max_signed(const ClaricppBackend z3, const ClaricppExpr expr,
                                       const ClaricppSolver solver);

/** Maximize a signed z3 expr subjects to the constraints of a solver
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to maximize
 *  @param solver The solver whose constraints expr must be subject to
 *  @param extra_constraints An array of extra constraints required be simultaneously satisfiable
 *  @param len The length of the extra_constraints array
 *  @return The value of expr when it is maximized subject to the solver
 */
int64_t claricpp_backend_z3_max_signed_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                          const ClaricppSolver solver,
                                          ARRAY_IN(ClaricppExpr) extra_constraints,
                                          const SIZE_T len);

/** Maximize a unsigned z3 expr subjects to the constraints of a solver
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to maximize
 *  @param solver The solver whose constraints expr must be subject to
 *  @return The value of expr when it is maximized subject to the solver
 */
uint64_t claricpp_backend_z3_max_unsigned(const ClaricppBackend z3, const ClaricppExpr expr,
                                          const ClaricppSolver solver);

/** Maximize a unsigned z3 expr subjects to the constraints of a solver
 *  @param z3 The Z3 backend to use
 *  @param expr The expr to maximize
 *  @param solver The solver whose constraints expr must be subject to
 *  @param extra_constraints An array of extra constraints required be simultaneously satisfiable
 *  @param len The length of the extra_constraints array
 *  @return The value of expr when it is maximized subject to the solver
 */
uint64_t claricpp_backend_z3_max_unsigned_ec(const ClaricppBackend z3, const ClaricppExpr expr,
                                             const ClaricppSolver solver,
                                             ARRAY_IN(ClaricppExpr) extra_constraints,
                                             const SIZE_T len);

/** Retrieves the unsat core of the solver
 *  Note: .arr of the return value points to a dynamically allocated array
 *  @param z3 The Z3 backend to use
 *  @param solver The solver to retrieve the unsat core from
 *  @return The array of constraints extract from the unsat core of solver and its size
 */
ARRAY_OUT(ClaricppExpr)
claricpp_backend_z3_unsat_core(const ClaricppBackend z3, const ClaricppSolver solver);

#if 0
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
