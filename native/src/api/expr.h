/**
 * @file
 * @brief This header defines the C API for Expr
 * \ingroup api
 */
#ifndef R_EXPR_H_
#define R_EXPR_H_

#include "constants.h"

/** Return a new Annotation::Base
 *  @param old The Expr to mostly copy
 *  @param ans The annotations this new base should have
 *  @return A ClaricppExpr that is a copy of old, except for its annotations
 */
ClaricppExpr claricpp_expr_make_like_annotations(const ClaricppExpr old, ClaricppSPAV spav);

/** Return true iff expr is symbolic
 * @param expr The Expr to determine if it is symbolic
 * @return True if expr is symbolic
 */
bool claricpp_expr_symbolic(const ClaricppExpr expr);

/** Return the SPAV expr holds
 * @param expr The Expr to get the SPAV of
 * @return The SPAV Expr holds, .ptr is set to NULL if the SPAV is nullptr
 */
ClaricppSPAV claricpp_expr_annotations(const ClaricppExpr expr);

/** Gets the bit length of expr
 *  @param expr The Expr to check the length of
 *  @return The bit length of expr
 */
SIZE_T claricpp_expr_bit_length(const ClaricppExpr expr);

/** Gets the args of expr
 *  @param expr The Expr to get the args of
 *  @return The args of expr
 */
ARRAY_OUT(ClaricppArg) claricpp_expr_args(const ClaricppExpr expr);

#endif
