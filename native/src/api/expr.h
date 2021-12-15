/**
 * @file
 * @brief This header defines the C API for Expr
 * \ingroup api
 */
#ifndef R_API_EXPR_H_
#define R_API_EXPR_H_

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
BOOL claricpp_expr_symbolic(const ClaricppExpr expr);

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

/** Get the repr of the expr
 * @param expr The expr to get the repr of
 * @return The repr of expr as a C string
 */
const char *claricpp_expr_repr(const ClaricppExpr expr);

/** Get the type name of the expr
 * @param expr The expr to get the type name of
 * @return The name of the type of expr as a C string
 */
const char *claricpp_expr_type_name(const ClaricppExpr expr);

/** Get the op name of the expr
 * @param expr The expr to get the op name of
 * @return The name of the op in expr as a C string
 */
const char *claricpp_expr_op_name(const ClaricppExpr expr);

/** Get the CUID of the expr
 * @param expr The expr to get the CUID of
 * @return The CUID of expr
 */
CUID_T claricpp_expr_cuid(const ClaricppExpr expr);

/** Get the CUID of the expr's op
 * @param expr The expr holding the op to get the CUID of
 * @return The CUID of expr's op
 */
CUID_T claricpp_expr_op_cuid(const ClaricppExpr expr);

#endif
