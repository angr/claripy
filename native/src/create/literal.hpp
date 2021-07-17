/**
 * @file
 * @brief This file defines a method to create an Expression with an literal Op
 */
#ifndef R_CREATE_LITERAL_HPP_
#define R_CREATE_LITERAL_HPP_

#include "private/literal.hpp"


namespace Create {

/** A local macro used for consistency */
#define TRIVIAL_TYPE(EXP, INPUT)                                                                  \
    inline EBasePtr literal(const INPUT data, SPAV &&sp = nullptr) {                              \
        return Private::literal<Expression::EXP, INPUT>(INPUT { data }, std::move(sp));           \
    }

/** A local macro used for consistency */
#define TRIVIAL_MOVE_TYPE(EXP, INPUT)                                                             \
    inline EBasePtr literal(INPUT &&data, SPAV &&sp = nullptr) {                                  \
        return Private::literal<Expression::EXP, INPUT>(std::move(data), std::move(sp));          \
    }

    /** Create a Bool Expression with a Literal op */
    TRIVIAL_TYPE(Bool, bool);

    /** Create a String Expression with a Literal op */
    TRIVIAL_MOVE_TYPE(String, std::string);

    /** Create a FP Expression with a Literal op containing a double precision float */
    TRIVIAL_TYPE(FP, double);

    /** Create a FP Expression with a Literal op containing a single precision float */
    TRIVIAL_TYPE(FP, float);

    /** Create a FP Expression with a Literal op containing a single precision float
     *  data may not be nullptr
     */
    TRIVIAL_MOVE_TYPE(VS, PyObj::VSPtr);

    // BV creation methods

    /** Create a BV Expression with a Literal op containing an 8-bit signed int */
    TRIVIAL_TYPE(BV, int8_t);
    /** Create a BV Expression with a Literal op containing an 16-bit signed int */
    TRIVIAL_TYPE(BV, int16_t);
    /** Create a BV Expression with a Literal op containing an 32-bit signed int */
    TRIVIAL_TYPE(BV, int32_t);
    /** Create a BV Expression with a Literal op containing an 64-bit signed int */
    TRIVIAL_TYPE(BV, int64_t);

    /** Create a BV Expression with a Literal op containing an 8-bit unsigned int */
    TRIVIAL_TYPE(BV, uint8_t);
    /** Create a BV Expression with a Literal op containing an 16-bit unsigned int */
    TRIVIAL_TYPE(BV, uint16_t);
    /** Create a BV Expression with a Literal op containing an 32-bit unsigned int */
    TRIVIAL_TYPE(BV, uint32_t);
    /** Create a BV Expression with a Literal op containing an 64-bit unsigned int */
    TRIVIAL_TYPE(BV, uint64_t);

    /** Create a BV Expression with a Literal op containing an arbitrary length int */
    TRIVIAL_MOVE_TYPE(VS, BigInt);

// Cleanup
#undef TRIVIAL_TYPE
#undef TRIVIAL_MOVE_TYPE

} // namespace Create

#endif
