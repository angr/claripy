/**
 * @file
 * @brief This header exposes the public C API for claricpp
 * Unless otherwise specified, arguments may not contain nullptr
 */
#ifndef R_APIPUBLIC_H_
#define R_APIPUBLIC_H_

#include <stddef.h>
#include <stdint.h>


/********************************************************************/
/*                        Type Declarations                         */
/********************************************************************/


/** Used to declare a C wrapper for a C++ type */
#define DECLARE_WRAPPER(NAME) \
    /** A C wrapper for a C++ type */ \
    struct NAME { void * ptr; }

DECLARE_WRAPPER(ClaricppAnnotation);
DECLARE_WRAPPER(ClaricppSPAV);
DECLARE_WRAPPER(ClaricppExpr);
DECLARE_WRAPPER(ClaricppBigInt);

/** Return the type of an input array of type T */
#define ARRAY_IN(T) const T * const

/** The type a Python string argument is */
typedef ARRAY_IN(char) PyStr;

/** Define SIZE_T as UInt without polluting the global namespace */
#define SIZE_T unsigned long long
/** Define Hash::Hash without polluting the global namespace */
#define HASH_T unsigned long long
/** Define a type python can pass to represent a VS within claricpp */
#define VS_T unsigned long long

// Cleanup
#undef DECLARE_WRAPPER


/********************************************************************/
/*                            Annotation                            */
/********************************************************************/


/** Return a new Annotation::Base */
ClaricppAnnotation claricpp_annotation_new_base();

/** Return a new Annotation::SimplificationAvoidance */
ClaricppAnnotation claricpp_annotation_new_simplification_avoicance();

/** Create an Annotation::SPAV from a list of annotations
 *  @param list An array of ClaricppAnnotation pointers
 *  @param len The length of list
 */
ClaricppSPAV claricpp_annotation_create_spav(ARRAY_IN(ClaricppAnnotation) list, const SIZE_T len);


/********************************************************************/
/*                              Create                              */
/********************************************************************/


// Symbol

/** Create an symbolic boolean expr
 *  @param name The name of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_symbol_bool(PyStr name, ClaricppSPAV spav);

/** Create an symbolic string expr
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_symbol_string(PyStr name, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create an symbolic VS expr
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_symbol_vs(PyStr name, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create an symbolic FP expr
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_symbol_fp(PyStr name, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create an symbolic BV expr
 *  @param name The name of the symbol
 *  @param bit_length The bit length of the symbol
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_symbol_bv(PyStr name, const SIZE_T bit_length, ClaricppSPAV spav);

// Literal

/** Create a literal bool expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_bool(const bool value, ClaricppSPAV spav);

/** Create a literal string expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_string(PyStr value, ClaricppSPAV spav);

/** Create a literal float expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_fp_float(const float value, ClaricppSPAV spav);

/** Create a literal double expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_fp_double(const double value, ClaricppSPAV spav);

/** Create a literal VS expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_vs(const HASH_T hash, const VS_T value, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create a literal uint8_t expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_bv_u8(const uint8_t value, ClaricppSPAV spav);

/** Create a literal uint16_t expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_bv_u16(const uint16_t value, ClaricppSPAV spav);

/** Create a literal uint32_t expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_bv_u32(const uint32_t value, ClaricppSPAV spav);

/** Create a literal uint64_t expr
 *  @param value The data held by the literal
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_bv_u64(const uint64_t value, ClaricppSPAV spav);

/** Create a literal BigInt expr with the BigInt in Str mode
 *  @param value The data held by the literal represented in base 10 by a string
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_bv_big_int_mode_str(PyStr value, const SIZE_T bit_length, ClaricppSPAV spav);

/** Create a literal BigInt expr with the BigInt in Int mode
 *  @param value The data held by the literal represented in base 10 by a string
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_literal_bv_big_int_mode_int(PyStr value, const SIZE_T bit_length, ClaricppSPAV spav);

// Non Trivial

/** Create an Extract Expr
 *  @param high The high index for the Extract op
 *  @param low The low index for the Extract op
 *  @param from The Expr to be extracted from
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_extract(const SIZE_T high, const SIZE_T low, const ClaricppExpr from, ClaricppSPAV spav);

/** Create an Extract Expr
 *  @param cond The condition expr
 *  @param left The 'if true' expr in the if then else statement
 *  @param left The 'if false' expr in the if then else statement
 *  @param spav A ClaricppSPAV; spav.ptr may be nullptr
 */
ClaricppExpr claricpp_create_if(const ClaricppExpr cond, const ClaricppExpr left, const ClaricppExpr right, ClaricppSPAV spav);

// Trivial

// String

// FP






/********************************************************************/
/*                               Expr                               */
/********************************************************************/


/********************************************************************/
/*                             Backend                              */
/********************************************************************/



#endif
