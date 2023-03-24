/**
 * @file
 * @brief This file defines a method to create an Expr with a literal Op
 */
#ifndef R_SRC_CREATE_LITERAL_HPP_
#define R_SRC_CREATE_LITERAL_HPP_

#include "private/literal.hpp"


// TODO: remove annotations from literals and symbol???
namespace Create {

    /** Create an Expr containing a literal op */
    template <typename T> Expr::BasePtr literal(T data) {
        return Private::literal(std::move(data), {});
    }

    /** Create an Expr containing a literal op with annotations */
    template <typename T> Expr::BasePtr literal(T data, Expr::OpPyDict &&d) {
        return Private::literal(std::move(data), std::move(d));
    }

    // Non-templated non-moving functions (the API can use these)

#define M_TRIVIAL_TYPE(NAME, INPUT)                                                                \
    inline Expr::BasePtr literal_##NAME(INPUT data, Expr::OpPyDict d = {}) {                       \
        return Private::literal<INPUT>(std::move(data), std::move(d));                             \
    }

    /** Create a Bool Expr with a Literal op */
    M_TRIVIAL_TYPE(bool, bool);

    /** Create a FP Expr with a Literal op containing a VS
     *  data may not be nullptr
     */
    M_TRIVIAL_TYPE(vs, PyObj::VS::Ptr);

    /** Create a FP Expr with a Literal op containing a String
     *  data may not be nullptr
     */
    M_TRIVIAL_TYPE(string, std::string);

#undef M_TRIVIAL_TYPE

    /** Create a String Expr with a Literal op with a specific size
     *  Note: data is implicitly padded with 0s on the right to meet length
     *  Note: length is taken in as a bit length, not a bit length
     */
    inline Expr::BasePtr literal_string(std::string data, const U64 bit_length,
                                        Expr::OpPyDict d = {}) {
        UTIL_ASSERT(Util::Err::Usage, (CHAR_BIT * bit_length) >= data.size(),
                    "Bit length must be large enough to hold the passed string");
        return Private::literal(std::move(data), std::move(d), bit_length);
    }

    // Order is the order that pybind11 will try them, common first!

    /** Create a FP Expr with a Literal op containing of bit length bit_length
     *  Warning: this may cast data to a smaller size (bit_length or greater)
     *  Note: bit_length instead of overrides or template b/c python bindings
     *  Specifically, only one override would ever be used
     *  TODO: later allow Width instead of bit_length (they should be the same size)
     */
    inline Expr::BasePtr literal_fp(const double data, const U64 bit_length,
                                    Expr::OpPyDict d = {}) {
        if (LIKELY(bit_length == 64)) {
            return Private::literal(data, std::move(d));
        }
        else if (LIKELY(bit_length == 32)) {
            return Private::literal(static_cast<float>(data), std::move(d));
        }
        UTIL_THROW(Util::Err::Usage, "Claricpp only supports 32 and 64 bit floats");
    }

    // We should support every BV creation method
    static_assert(std::variant_size_v<Op::BVVar> == 5,
                  "There should be more / less creation methods");

    /** Create a BV Expr with a Literal op of a given bit length from a U64
     *  Warning: this may cast data to a smaller size (bit_length or greater)
     *  Note: bit_length instead of overrides or template b/c python bindings
     *  Specifically: pybind11 tries methods in order, so we'd have to be very
     *  careful to ensure U8 methods were defined before U16, etc; then using
     *  U64 would fail 4 overrides and be slow.
     */
    inline Expr::BasePtr literal_bv(const U64 data, const U64 bit_length, Expr::OpPyDict d = {}) {
#define M_CASE(LEN, TO)                                                                            \
    case (LEN):                                                                                    \
        return Private::literal(static_cast<TO>(data), std::move(d));
        // Prefer native types
        switch (bit_length) {
            M_CASE(64, U64);
            M_CASE(32, uint32_t);
            M_CASE(16, uint16_t);
            M_CASE(8, uint8_t);
            default:
                return Private::literal(BigInt::from_int(data, bit_length), std::move(d));
        }
#undef M_CASE
    }

    /** Create a BV Expr with a Literal op from a BigInt */
    inline Expr::BasePtr literal_bv(BigInt data, Expr::OpPyDict d = {}) {
        return Private::literal(std::move(data), std::move(d));
    }

    /** Create a BV Expr with a Literal op containing an arbitrary length int
     *  Warning: this may cast data to a smaller size (bit_length or greater)
     *  data should be a base 10 string containing
     */
    inline Expr::BasePtr literal_bv(std::string data, const U64 bit_length, Expr::OpPyDict d = {}) {
#define M_CASE(LEN, TO)                                                                            \
    case (LEN):                                                                                    \
        return Private::literal(static_cast<TO>(std::stoull(std::move(data))), std::move(d));
        // Prefer native types
        switch (bit_length) {
            M_CASE(64, U64);
            M_CASE(32, uint32_t);
            M_CASE(16, uint16_t);
            M_CASE(8, uint8_t);
            default:
                return Private::literal(BigInt::from_str(std::move(data), bit_length),
                                        std::move(d));
        }
#undef M_CASE
    }

    /** This function exists to prevent accidental use by explicit rejection */
    inline Expr::BasePtr literal(CCSC, Expr::OpPyDict = {}) {
        UTIL_THROW(Util::Err::Usage, "Do not pass a char * to literal(); C++ casts it to bool; did "
                                     "you mean to use std::string?");
    }

} // namespace Create

#endif
