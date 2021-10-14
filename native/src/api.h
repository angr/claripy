/**
 * @file
 * @brief This header exposes the C API for claricpp
 */
#ifndef R_API_H_
#define R_API_H_

#include <stddef.h>
#include <stdint.h>

/********************************************************************/
/*                    Forward Type Declarations                     */
/********************************************************************/

/** Holds an Annotation::BasePtr */
struct ClaricppAnnotation;
/** Holds an Annotation::SPAV */
struct ClaricppSPAV;
/** Holds an Expression::Expr */
struct ClaricppExpr;
/** Holds a BigInt */
struct ClaricppBigInt;

/** Define SIZE_T as Constants::UInt without polluting the global namespace */
#define SIZE_T unsigned long long
/** Define Hash::Hash without polluting the global namespace */
#define HASH_T unsigned long long
/** Define a type python can pass to represent a VS within claricpp */
#define VS_T unsigned long long

/********************************************************************/
/*                            Annotation                            */
/********************************************************************/

/** Return a new Annotation::Base */
ClaricppAnnotation * claricpp_annotation_new_base();

/** Return a new Annotation::SimplificationAvoidance */
ClaricppAnnotation * claricpp_annotation_new_simplification_avoicance();

/** Create an Annotation::SPAV from a list of annotations
 *  @param list An array of ClaricppAnnotation pointers
 *  @param len The length of list
 */
ClaricppSPAV * claricpp_annotation_create_spav(const ClaricppAnnotation * const * const list, const SIZE_T len);

/********************************************************************/
/*                              Create                              */
/********************************************************************/

// Symbol

/** Create an symbolic boolean expression
 *  @param name The name of the symbol
 */
ClaricppExpr * claricpp_create_symbol_bool(const char * const name);

/** Create an symbolic string expression
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 */
ClaricppExpr * claricpp_create_symbol_string(const char * const name, const SIZE_T bit_length);

/** Create an symbolic VS expression
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 */
ClaricppExpr * claricpp_create_symbol_vs(const char * const name, const SIZE_T bit_length);

/** Create an symbolic FP expression
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 */
ClaricppExpr * claricpp_create_symbol_fp(const char * const name, const SIZE_T bit_length);

/** Create an symbolic BV expression
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 */
ClaricppExpr * claricpp_create_symbol_bv(const char * const name, const SIZE_T bit_length);

// Literal

/** Create a literal bool expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_bool(const bool value);

/** Create a literal string expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_string(const char * const value);

/** Create a literal float expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_fp_float(const float value);

/** Create a literal double expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_fp_double(const double value);

/** Create a literal VS expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_vs(const HASH_T hash, const VS_T value, const SIZE_T bit_length);

/** Create a literal uint8_t expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_bv_u8(const uint8_t value);

/** Create a literal uint16_t expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_bv_u16(const uint16_t value);

/** Create a literal uint32_t expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_bv_u32(const uint32_t value);

/** Create a literal uint64_t expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_bv_u64(const uint64_t value);

/** Create a literal uint64_t expression
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_bv_u64(const uint64_t value);

/** Create a literal double expression
 *  @todo : BigInt
 *  @param value The data held by the literal
 */
ClaricppExpr * claricpp_create_literal_bv_big_int(const ClaricppBigInt value);

/********************************************************************/
/*                            Expression                            */
/********************************************************************/

/********************************************************************/
/*                             Backend                              */
/********************************************************************/



#endif