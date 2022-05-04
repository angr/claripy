/**
 * @file
 * @brief Constants OPs can use
 */
#ifndef R_SRC_OP_CONSTANTS_HPP_
#define R_SRC_OP_CONSTANTS_HPP_

#include "../big_int.hpp"
#include "../expr.hpp"
#include "../py_obj.hpp"

#include <cstddef>
#include <stack>
#include <variant>


namespace Op {

    /** A vector back stacked of raw expression pointers which Op uses */
    using Stack = std::stack<Expr::RawPtr, std::vector<Expr::RawPtr>>;

    /** The primitive types a claricpp BV will support */
    using BVTL = Util::Type::List<uint8_t, uint16_t, uint32_t, U64, BigInt>;

    /** A variant of the types a claricpp BV can hold */
    using BVVar = BVTL::Apply<std::variant>;

    /** The types a primitive can support */
    using PrimTL = BVTL::Prepend<bool,          // Bool
                                 std::string,   // String
                                 float, double, // FP
                                 PyObj::VS::Ptr // VS
                                 >;

    /** A variant of the types a primitive can support */
    using PrimVar = PrimTL::Apply<std::variant>;

    /** Every type a claricpp public data member may be */
    using ArgTL = PrimTL::Append<Expr::BasePtr, Mode::FP::Rounding, Mode::FP::Width>;

    /** A variant of the every type a claricpp data member may be */
    using ArgVar = ArgTL::Apply<std::variant>;

    // Checks
    static_assert(std::is_copy_constructible_v<ArgVar>, "Fix me");
    static_assert(std::is_copy_assignable_v<ArgVar>, "Fix me");

    /** Returns the bit_length of the value stored in Data
     *  Raise an exception if called on a size without a bitlength (like a bool)
     */
    inline U64 bit_length(const PrimVar &v) {
        static_assert(std::variant_size_v<PrimVar> == 10);
        switch (v.index()) {
#define M_CASE(TYPE, EXPR)                                                                         \
    case (Util::Type::index<PrimVar, TYPE>): {                                                     \
        const auto &got { std::get<TYPE>(v) };                                                     \
        return EXPR;                                                                               \
    }
            M_CASE(std::string, CHAR_BIT * got.size());
            M_CASE(float, CHAR_BIT * sizeof(got));
            M_CASE(double, CHAR_BIT * sizeof(got));
            M_CASE(PyObj::VS::Ptr, got->bit_length);
            M_CASE(uint8_t, CHAR_BIT * sizeof(got));
            M_CASE(uint16_t, CHAR_BIT * sizeof(got));
            M_CASE(uint32_t, CHAR_BIT * sizeof(got));
            M_CASE(U64, CHAR_BIT * sizeof(got));
            M_CASE(BigInt, got.bit_length);
#undef M_CASE
            // bool
            default: {
                UTIL_THROW(Util::Err::Usage,
                           "invoked when internal type does not correspond to an Expr which "
                           "subclasses BitLength. Current variant index is: ",
                           v.index());
            };
        }
    }

} // namespace Op

#endif
