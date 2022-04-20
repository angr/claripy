/**
 * @file
 * @brief This file defines a method to create an Expr with an literal Op
 */
#ifndef R_SRC_CREATE_LITERAL_HPP_
#define R_SRC_CREATE_LITERAL_HPP_

#include "private/literal.hpp"


namespace Create {

    /** This function exists to prevent accidental use by explicit rejection */
    inline Expr::BasePtr literal(CCSC, Annotation::SPAV = empty_spav) {
        UTIL_THROW(Util::Err::Usage, "Do not pass a char * to literal(); C++ casts it to bool; did "
                                     "you mean to use std::string?");
    }

/** A local macro used for consistency */
#define TRIVIAL_BUILTIN_TYPE(EXP, INPUT)                                                           \
    inline Expr::BasePtr literal(const INPUT data, Annotation::SPAV sp = empty_spav) {             \
        return Private::literal<Expr::EXP, INPUT>(INPUT { data }, std::move(sp));                  \
    }

/** A local macro used for consistency */
#define TRIVIAL_TYPE(EXP, INPUT)                                                                   \
    inline Expr::BasePtr literal(INPUT data, Annotation::SPAV sp = empty_spav) {                   \
        return Private::literal<Expr::EXP, INPUT>(std::move(data), std::move(sp));                 \
    }

    /** Create a Bool Expr with a Literal op */
    TRIVIAL_BUILTIN_TYPE(Bool, bool);

    /** Create a String Expr with a Literal op */
    TRIVIAL_TYPE(String, std::string);

    /** Create a FP Expr with a Literal op containing a double precision float */
    TRIVIAL_BUILTIN_TYPE(FP, double);

    /** Create a FP Expr with a Literal op containing a single precision float */
    TRIVIAL_BUILTIN_TYPE(FP, float);

    /** Create a FP Expr with a Literal op containing a single precision float
     *  data may not be nullptr
     */
    TRIVIAL_TYPE(VS, PyObj::VSPtr);

    // BV creation methods

    /** Create a BV Expr with a Literal op containing an 8-bit unsigned int */
    TRIVIAL_BUILTIN_TYPE(BV, uint8_t);
    /** Create a BV Expr with a Literal op containing an 16-bit unsigned int */
    TRIVIAL_BUILTIN_TYPE(BV, uint16_t);
    /** Create a BV Expr with a Literal op containing an 32-bit unsigned int */
    TRIVIAL_BUILTIN_TYPE(BV, uint32_t);
    /** Create a BV Expr with a Literal op containing an 64-bit unsigned int */
    TRIVIAL_BUILTIN_TYPE(BV, U64);

    /** Create a BV Expr with a Literal op containing an arbitrary length int */
    TRIVIAL_TYPE(BV, BigInt);

// Cleanup
#undef TRIVIAL_BUILTIN_TYPE
#undef TRIVIAL_TYPE

} // namespace Create

#endif
