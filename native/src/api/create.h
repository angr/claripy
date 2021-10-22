/**
 * @file
 * @brief This header defines the C API for Create
 */
#ifndef R_API_CREATE_H_
#define R_API_CREATE_H_

#include "constants.h"


/********************************************************************/
/*                              Symbol                              */
/********************************************************************/

/** Create an symbolic boolean expr
 *  @param name The name of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a boolean symbol
 */
ClaricppExpr claricpp_create_symbol_bool(PyStr name, ClaricppSPAV spav);

/** Create an symbolic string expr
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a string symbol
 */
ClaricppExpr claricpp_create_symbol_string(PyStr name, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create an symbolic VS expr
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a value set symbol
 */
ClaricppExpr claricpp_create_symbol_vs(PyStr name, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create an symbolic FP expr
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a floating point symbol
 */
ClaricppExpr claricpp_create_symbol_fp(PyStr name, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create an symbolic BV expr
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a bit vector symbol
 */
ClaricppExpr claricpp_create_symbol_bv(PyStr name, const SIZE_T bit_length, ClaricppSPAV spav);

/********************************************************************/
/*                             Literal                              */
/********************************************************************/

/** Create a literal bool expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a bool constant
 */
ClaricppExpr claricpp_create_literal_bool(const bool value, ClaricppSPAV spav);

/** Create a literal string expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a string constant
 */
ClaricppExpr claricpp_create_literal_string(PyStr value, ClaricppSPAV spav);

/** Create a literal float expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a 32-bit float constant
 */
ClaricppExpr claricpp_create_literal_fp_float(const float value, ClaricppSPAV spav);

/** Create a literal double expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a 64-bit float constant
 */
ClaricppExpr claricpp_create_literal_fp_double(const double value, ClaricppSPAV spav);

/** Create a literal VS expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a value set constant
 */
ClaricppExpr claricpp_create_literal_vs(const HASH_T hash, const VS_T value, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create a literal uint8_t expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an 8-bit bit vector constant
 */
ClaricppExpr claricpp_create_literal_bv_u8(const uint8_t value, ClaricppSPAV spav);

/** Create a literal uint16_t expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an 16-bit bit vector constant
 */
ClaricppExpr claricpp_create_literal_bv_u16(const uint16_t value, ClaricppSPAV spav);

/** Create a literal uint32_t expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an 32-bit bit vector constant
 */
ClaricppExpr claricpp_create_literal_bv_u32(const uint32_t value, ClaricppSPAV spav);

/** Create a literal uint64_t expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an 64-bit bit vector constant
 */
ClaricppExpr claricpp_create_literal_bv_u64(const uint64_t value, ClaricppSPAV spav);

/** Create a literal BigInt expr with the BigInt in Str mode
 *  @param value The data held by the literal represented in base 10 by a string
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a BigInt bit vector constant stored in string form
 */
ClaricppExpr claricpp_create_literal_bv_big_int_mode_str(PyStr value, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create a literal BigInt expr with the BigInt in Int mode
 *  @param value The data held by the literal represented in base 10 by a string
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a BigInt bit vector constant stored in int form
 */
ClaricppExpr claricpp_create_literal_bv_big_int_mode_int(PyStr value, const SIZE_T bit_length, ClaricppSPAV spav);

/********************************************************************/
/*                           Non-Trivial                            */
/********************************************************************/

/** Create an Extract Expr
 *  @param high The high index for the Extract op
 *  @param low The low index for the Extract op
 *  @param from The BV Expr to be extracted from
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an Extract expression
 */
ClaricppExpr claricpp_create_extract(const SIZE_T high, const SIZE_T low, const ClaricppExpr from, ClaricppSPAV spav);

/** Create an if-then-else Expr
 *  @param cond The condition expr
 *  @param left The 'if true' expr in the if then else statement
 *  @param right The 'if false' expr in the if then else statement
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an if-then-else expression
 */
ClaricppExpr claricpp_create_if(const ClaricppExpr cond, const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/********************************************************************/
/*                          Trivial Unary                           */
/********************************************************************/

/** Create an abs Expr
 *  @param x The expression take the absolute value of
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an abs expression
 */
ClaricppExpr claricpp_create_abs(const ClaricppExpr x, ClaricppSPAV spav);

/** Create a neg Expr
 *  @param x The expression to be negated
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a neg expression
 */
ClaricppExpr claricpp_create_neg(const ClaricppExpr x, ClaricppSPAV spav);

/** Create a not Expr
 *  @param x The expression to be not-ed
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a not expression
 */
ClaricppExpr claricpp_create_not(const ClaricppExpr x, ClaricppSPAV spav);

/** Create a not Expr
 *  @param x The expression to be inverted
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an invert expression
 */
ClaricppExpr claricpp_create_invert(const ClaricppExpr x, ClaricppSPAV spav);

/** Create a not Expr
 *  @param x The expression to be reversed
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a reverse expression
 */
ClaricppExpr claricpp_create_reverse(const ClaricppExpr x, ClaricppSPAV spav);

/********************************************************************/
/*                        Trivial UInt Binary                       */
/********************************************************************/

/** Create a sign extension Expr
 *  @param expr The expression to be reversed
 *  @param integer The number of bits to extend expr by
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a sign_ext expression
 */
ClaricppExpr claricpp_create_sign_ext(const ClaricppExpr expr, const UINT integer, ClaricppSPAV spav);

/** Create a zero extension Expr
 *  @param expr The expression to be reversed
 *  @param integer The number of bits to extend expr by
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a zero_ext expression
 */
ClaricppExpr claricpp_create_zero_ext(const ClaricppExpr expr, const UINT integer, ClaricppSPAV spav);

/********************************************************************/
/*                          Trivial Binary                          */
/********************************************************************/

// Comparisons

/** Create an eq Expr
 *  @param left The left operands of the == Expr
 *  @param right The left operands of the == Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an eq expression
 */
ClaricppExpr claricpp_create_eq(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create an neq Expr
 *  @param left The left operands of the != Expr
 *  @param right The left operands of the != Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an neq expression
 */
ClaricppExpr claricpp_create_neq(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a signed less than Expr
 *  @param left The left operands of the signed < Expr
 *  @param right The left operands of the signed < Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed less than expression
 */
ClaricppExpr claricpp_create_slt(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a signed less or equal Expr
 *  @param left The left operands of the signed <= Expr
 *  @param right The left operands of the signed <= Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed less or equal expression
 */
ClaricppExpr claricpp_create_sle(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a signed greater than Expr
 *  @param left The left operands of the signed > Expr
 *  @param right The left operands of the signed > Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed greater than expression
 */
ClaricppExpr claricpp_create_sgt(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a signed greater or equal Expr
 *  @param left The left operands of the signed >= Expr
 *  @param right The left operands of the signed >= Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed greater or equal expression
 */
ClaricppExpr claricpp_create_sge(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a unsigned less than Expr
 *  @param left The left operands of the unsigned < Expr
 *  @param right The left operands of the unsigned < Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned less than expression
 */
ClaricppExpr claricpp_create_ult(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a unsigned less or equal Expr
 *  @param left The left operands of the unsigned <= Expr
 *  @param right The left operands of the unsigned <= Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned less or equal expression
 */
ClaricppExpr claricpp_create_ule(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a unsigned greater than Expr
 *  @param left The left operands of the unsigned > Expr
 *  @param right The left operands of the unsigned > Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned greater than expression
 */
ClaricppExpr claricpp_create_ugt(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a unsigned greater or equal Expr
 *  @param left The left operands of the unsigned >= Expr
 *  @param right The left operands of the unsigned >= Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned greater or equal expression
 */
ClaricppExpr claricpp_create_uge(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

// Math

/** Create a subtraction Expr
 *  @param left The left operands of the subtraction Expr
 *  @param right The left operands of the subtraction Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a subtraction expression
 */
ClaricppExpr claricpp_create_sub(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a signed division Expr
 *  @param left The left operands of the signed division Expr
 *  @param right The left operands of the signed division Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed division expression
 */
ClaricppExpr claricpp_create_sdiv(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a unsigned division Expr
 *  @param left The left operands of the unsigned division Expr
 *  @param right The left operands of the unsigned division Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned division expression
 */
ClaricppExpr claricpp_create_udiv(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a signed mod Expr
 *  @param left The left operands of the signed mod Expr
 *  @param right The left operands of the signed mod Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed mod expression
 */
ClaricppExpr claricpp_create_smod(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a unsigned mod Expr
 *  @param left The left operands of the unsigned mod Expr
 *  @param right The left operands of the unsigned mod Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned mod expression
 */
ClaricppExpr claricpp_create_umod(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

// Bitwise

enum class Shift { Left, LogicalRight, ArithmeticRight };
/** Create a shift left Expr
 *  @param left The left operands of the shift Expr
 *  @param right The left operands of the shift Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a left shift expression
 */
ClaricppExpr claricpp_create_shift_left(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a shift logical right Expr
 *  @param left The left operands of the shift Expr
 *  @param right The left operands of the shift Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a logical right shift expression
 */
ClaricppExpr claricpp_create_shift_logical_right(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

/** Create a shift arithmetic right Expr
 *  @param left The left operands of the shift Expr
 *  @param right The left operands of the shift Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a left shift expression
 */
ClaricppExpr claricpp_create_shift_arithmetic_right(const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

// Misc


#if 0
/** Create an Expr with a Shift op
     *  Expr pointers may not be nullptr
 */
template <Mode::Shift Mask>
inline Expr::BasePtr shift(const Expr::BasePtr &left, const Expr::BasePtr &right,
                           Annotation::SPAV &&sp = nullptr);
/** Create an Expr with a Rotate op
     *  Expr pointers may not be nullptr
 */
template <Mode::LR LR>
inline Expr::BasePtr rotate(const Expr::BasePtr &left, const Expr::BasePtr &right,
                            Annotation::SPAV &&sp = nullptr);
// Misc

/** Create an Expr with an Widen op
     *  Expr pointers may not be nullptr
 */
inline Expr::BasePtr widen(const Expr::BasePtr &left, const Expr::BasePtr &right,
                           Annotation::SPAV &&sp = nullptr);
/** Create an Expr with an Union op
     *  Expr pointers may not be nullptr
 */
inline Expr::BasePtr union_(const Expr::BasePtr &left, const Expr::BasePtr &right,
                            Annotation::SPAV &&sp = nullptr);
/** Create an Expr with an Intersection op
     *  Expr pointers may not be nullptr
 */
inline Expr::BasePtr intersection_(const Expr::BasePtr &left, const Expr::BasePtr &right,
                                   Annotation::SPAV &&sp = nullptr);
/** Create an Expr with an Concat op
     *  Expr pointers may not be nullptr
 */
inline Expr::BasePtr concat(const Expr::BasePtr &left, const Expr::BasePtr &right,
                            Annotation::SPAV &&sp = nullptr);
#endif

/********************************************************************/
/*                         Trivial Trinary                          */
/********************************************************************/

// String

// FP

#endif
