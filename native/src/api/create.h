/**
 * @file
 * @brief This header defines the C API for Create
 * \ingroup api
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
ClaricppExpr claricpp_create_literal_bool(const BOOL value, ClaricppSPAV spav);

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
ClaricppExpr claricpp_create_literal_vs(const HASH_T hash, const VS_T value,
                                        const SIZE_T bit_length, ClaricppSPAV spav);

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
ClaricppExpr claricpp_create_literal_bv_big_int_mode_str(PyStr value, const SIZE_T bit_length,
                                                         ClaricppSPAV spav);

/** Create a literal BigInt expr with the BigInt in Int mode
 *  @param value The data held by the literal represented in base 10 by a string
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a BigInt bit vector constant stored in int form
 */
ClaricppExpr claricpp_create_literal_bv_big_int_mode_int(PyStr value, const SIZE_T bit_length,
                                                         ClaricppSPAV spav);

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
ClaricppExpr claricpp_create_extract(const SIZE_T high, const SIZE_T low, const ClaricppExpr from,
                                     ClaricppSPAV spav);

/** Create an if-then-else Expr
 *  @param cond The condition expr
 *  @param if_true The 'if true' expr in the if then else statement
 *  @param if_false The 'if false' expr in the if then else statement
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an if-then-else expression
 */
ClaricppExpr claricpp_create_if(const ClaricppExpr cond, const ClaricppExpr if_true,
                                const ClaricppExpr if_false, ClaricppSPAV spav);

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
 *  @param add The number of bits to extend expr by
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a sign_ext expression
 */
ClaricppExpr claricpp_create_sign_ext(const ClaricppExpr expr, const UINT add, ClaricppSPAV spav);

/** Create a zero extension Expr
 *  @param expr The expression to be reversed
 *  @param add The number of bits to extend expr by
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a zero_ext expression
 */
ClaricppExpr claricpp_create_zero_ext(const ClaricppExpr expr, const UINT add, ClaricppSPAV spav);

/********************************************************************/
/*                          Trivial Binary                          */
/********************************************************************/

// Comparisons

/** Create an eq Expr
 *  @param left The left operand of the == Expr
 *  @param right The right operand of the == Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an eq expression
 */
ClaricppExpr claricpp_create_eq(const ClaricppExpr left, const ClaricppExpr right,
                                ClaricppSPAV spav);

/** Create an neq Expr
 *  @param left The left operand of the != Expr
 *  @param right The right operand of the != Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an neq expression
 */
ClaricppExpr claricpp_create_neq(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a signed less than Expr
 *  @param left The left operand of the signed < Expr
 *  @param right The right operand of the signed < Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed less than expression
 */
ClaricppExpr claricpp_create_slt(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a signed less or equal Expr
 *  @param left The left operand of the signed <= Expr
 *  @param right The right operand of the signed <= Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed less or equal expression
 */
ClaricppExpr claricpp_create_sle(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a signed greater than Expr
 *  @param left The left operand of the signed > Expr
 *  @param right The right operand of the signed > Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed greater than expression
 */
ClaricppExpr claricpp_create_sgt(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a signed greater or equal Expr
 *  @param left The left operand of the signed >= Expr
 *  @param right The right operand of the signed >= Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed greater or equal expression
 */
ClaricppExpr claricpp_create_sge(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a unsigned less than Expr
 *  @param left The left operand of the unsigned < Expr
 *  @param right The right operand of the unsigned < Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned less than expression
 */
ClaricppExpr claricpp_create_ult(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a unsigned less or equal Expr
 *  @param left The left operand of the unsigned <= Expr
 *  @param right The right operand of the unsigned <= Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned less or equal expression
 */
ClaricppExpr claricpp_create_ule(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a unsigned greater than Expr
 *  @param left The left operand of the unsigned > Expr
 *  @param right The right operand of the unsigned > Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned greater than expression
 */
ClaricppExpr claricpp_create_ugt(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a unsigned greater or equal Expr
 *  @param left The left operand of the unsigned >= Expr
 *  @param right The right operand of the unsigned >= Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned greater or equal expression
 */
ClaricppExpr claricpp_create_uge(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

// Math

/** Create a subtraction Expr
 *  @param left The left operand of the subtraction Expr
 *  @param right The right operand of the subtraction Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a subtraction expression
 */
ClaricppExpr claricpp_create_sub(const ClaricppExpr left, const ClaricppExpr right,
                                 ClaricppSPAV spav);

/** Create a signed division Expr
 *  @param left The left operand of the signed division Expr
 *  @param right The right operand of the signed division Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed division expression
 */
ClaricppExpr claricpp_create_sdiv(const ClaricppExpr left, const ClaricppExpr right,
                                  ClaricppSPAV spav);

/** Create a unsigned division Expr
 *  @param left The left operand of the unsigned division Expr
 *  @param right The right operand of the unsigned division Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned division expression
 */
ClaricppExpr claricpp_create_udiv(const ClaricppExpr left, const ClaricppExpr right,
                                  ClaricppSPAV spav);

/** Create a signed mod Expr
 *  @param left The left operand of the signed mod Expr
 *  @param right The right operand of the signed mod Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a signed mod expression
 */
ClaricppExpr claricpp_create_smod(const ClaricppExpr left, const ClaricppExpr right,
                                  ClaricppSPAV spav);

/** Create a unsigned mod Expr
 *  @param left The left operand of the unsigned mod Expr
 *  @param right The right operand of the unsigned mod Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a unsigned mod expression
 */
ClaricppExpr claricpp_create_umod(const ClaricppExpr left, const ClaricppExpr right,
                                  ClaricppSPAV spav);

// Bitwise

/** Create a shift left Expr
 *  @param left The left operand of the shift Expr
 *  @param right The right operand of the shift Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a left shift expression
 */
ClaricppExpr claricpp_create_shift_left(const ClaricppExpr left, const ClaricppExpr right,
                                        ClaricppSPAV spav);

/** Create a shift logical right Expr
 *  @param left The left operand of the shift Expr
 *  @param right The right operand of the shift Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a logical right shift expression
 */
ClaricppExpr claricpp_create_shift_logical_right(const ClaricppExpr left, const ClaricppExpr right,
                                                 ClaricppSPAV spav);

/** Create a shift arithmetic right Expr
 *  @param left The left operand of the shift Expr
 *  @param right The right operand of the shift Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an arithmetic right shift expression
 */
ClaricppExpr claricpp_create_shift_arithmetic_right(const ClaricppExpr left,
                                                    const ClaricppExpr right, ClaricppSPAV spav);

// Misc

/** Create a widen Expr
 *  @param left The left operand of the widen Expr
 *  @param right The right operand of the widen Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a widen expression
 */
ClaricppExpr claricpp_create_widen(const ClaricppExpr left, const ClaricppExpr right,
                                   ClaricppSPAV spav);

/** Create a union Expr
 *  @param left The left operand of the union Expr
 *  @param right The right operand of the union Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a union expression
 */
ClaricppExpr claricpp_create_union(const ClaricppExpr left, const ClaricppExpr right,
                                   ClaricppSPAV spav);

/** Create a intersection Expr
 *  @param left The left operand of the intersection Expr
 *  @param right The right operand of the intersection Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a intersection expression
 */
ClaricppExpr claricpp_create_intersection(const ClaricppExpr left, const ClaricppExpr right,
                                          ClaricppSPAV spav);

/** Create a concat Expr
 *  @param left The left operand of the concat Expr
 *  @param right The right operand of the concat Expr
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a concat expression
 */
ClaricppExpr claricpp_create_concat(const ClaricppExpr left, const ClaricppExpr right,
                                    ClaricppSPAV spav);

/********************************************************************/
/*                               Flat                               */
/********************************************************************/

// Math

/** Create an add Expr
 *  @param operands A list of ClaricppExprs that are the operands to add
 *  @param len The length of the operands array
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an add expression
 */
ClaricppExpr claricpp_create_add(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                 ClaricppSPAV spav);

/** Create an mul Expr
 *  @param operands A list of ClaricppExprs that are the operands to mul
 *  @param len The length of the operands array
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an mul expression
 */
ClaricppExpr claricpp_create_mul(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                 ClaricppSPAV spav);

// Logical

/** Create an or Expr
 *  @param operands A list of ClaricppExprs that are the operands to or
 *  @param len The length of the operands array
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an or expression
 */
ClaricppExpr claricpp_create_or(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                ClaricppSPAV spav);

/** Create an and Expr
 *  @param operands A list of ClaricppExprs that are the operands to and
 *  @param len The length of the operands array
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an and expression
 */
ClaricppExpr claricpp_create_and(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                 ClaricppSPAV spav);

/** Create an xor Expr
 *  @param operands A list of ClaricppExprs that are the operands to xor
 *  @param len The length of the operands array
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an xor expression
 */
ClaricppExpr claricpp_create_xor(ARRAY_IN(ClaricppExpr) operands, const SIZE_T len,
                                 ClaricppSPAV spav);

/********************************************************************/
/*                              String                              */
/********************************************************************/

// Unary

/** Create a String::is_digit Expr
 *  @param x The String to be checked if it is a digit or not
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a String::is_digit expression
 */
ClaricppExpr claricpp_create_string_is_digit(const ClaricppExpr x, ClaricppSPAV spav);

// UInt Binary

/** Create a String::to_int Expr
 *  @param expr The String to be converted to a BV
 *  @param len The bit length of the resulting BV
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a String::to_int expression
 */
ClaricppExpr claricpp_create_string_to_int(const ClaricppExpr expr, const UINT len,
                                           ClaricppSPAV spav);

/** Create a String::len Expr
 *  @param expr The String to measure the length of
 *  @param len The bit length of the resulting BV
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a String::len expression
 */
ClaricppExpr claricpp_create_string_len(const ClaricppExpr expr, const UINT len, ClaricppSPAV spav);

// Binary

/** Create a String::contains Expr
 *  @param left The String to be searched
 *  @param right The String to search for
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a String::contains expression
 */
ClaricppExpr claricpp_create_string_contains(const ClaricppExpr full, const ClaricppExpr sub,
                                             ClaricppSPAV spav);

/** Create a String::prefix_of Expr
 *  @param left The String to be searched
 *  @param right The String prefix to check for
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a String::prefix_of expression
 */
ClaricppExpr claricpp_create_string_prefix_of(const ClaricppExpr full, const ClaricppExpr prefix,
                                              ClaricppSPAV spav);

/** Create a String::suffix_of Expr
 *  @param left The String to be searched
 *  @param right The String suffix to check for
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a String::suffix_of expression
 */
ClaricppExpr claricpp_create_string_suffix_of(const ClaricppExpr full, const ClaricppExpr suffix,
                                              ClaricppSPAV spav);

/********************************************************************/
/*                                FP                                */
/********************************************************************/

// Unary

/** Create an FP::to_ieee_bv Expr
 *  @param x The FP to be converted into a BV
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing a FP::to_ieee_bv expression
 */
ClaricppExpr claricpp_create_fp_to_ieee_bv(const ClaricppExpr x, ClaricppSPAV spav);

// Mode Binary

/** Create an FP::add Expr
 *  @param left The left FP operand of the add function
 *  @param right The left FP operand of the add function
 *  @param mode The FP rounding mode to be used while adding
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an FP::add expression
 */
ClaricppExpr claricpp_create_fp_add(const ClaricppExpr left, const ClaricppExpr right,
                                    const ClaricppRM mode, ClaricppSPAV spav);

/** Create an FP::sub Expr
 *  @param left The left FP operand of the sub function
 *  @param right The left FP operand of the sub function
 *  @param mode The FP rounding mode to be used while adding
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an FP::sub expression
 */
ClaricppExpr claricpp_create_fp_sub(const ClaricppExpr left, const ClaricppExpr right,
                                    const ClaricppRM mode, ClaricppSPAV spav);

/** Create an FP::mul Expr
 *  @param left The left FP operand of the mul function
 *  @param right The left FP operand of the mul function
 *  @param mode The FP rounding mode to be used while adding
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an FP::mul expression
 */
ClaricppExpr claricpp_create_fp_mul(const ClaricppExpr left, const ClaricppExpr right,
                                    const ClaricppRM mode, ClaricppSPAV spav);

/** Create an FP::div Expr
 *  @param left The left FP operand of the div function
 *  @param right The left FP operand of the div function
 *  @param mode The FP rounding mode to be used while adding
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 *  @return A ClaricppExpr containing an FP::div expression
 */
ClaricppExpr claricpp_create_fp_div(const ClaricppExpr left, const ClaricppExpr right,
                                    const ClaricppRM mode, ClaricppSPAV spav);

#endif