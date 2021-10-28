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

/** Gets the bit length of expr
 *  @param expr The Expr to check the length of
 *  @return The bit length of expr
 */
SIZE_T claricpp_expr_bit_length(const ClaricppExpr expr);

#endif
