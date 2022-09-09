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

    /** A variant of the types a primitive can be */
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

#define M_CASE(TYPE, EXPR)                                                                         \
    case (Util::Type::index<PrimVar, TYPE>): {                                                     \
        const auto &got { std::get<TYPE>(v) };                                                     \
        return EXPR;                                                                               \
    }

    /** Returns the bit_length of the value stored in v if applicable
     *  Note: this is a raw bit_length that does not include implicit null-padding
     *  This means for strings, the op bit_length may be shorter than the expr bit length
     *  Raise an exception if called on a size without a bit length (like a bool)
     */
    inline U64 bit_length(const PrimVar &v) {
        static_assert(std::variant_size_v<PrimVar> == 10, "Fix me");
        switch (v.index()) {
            M_CASE(std::string, CHAR_BIT * got.size());
            M_CASE(float, CHAR_BIT * sizeof(got));
            M_CASE(double, CHAR_BIT * sizeof(got));
            M_CASE(PyObj::VS::Ptr, got->bit_length);
            M_CASE(uint8_t, CHAR_BIT * sizeof(got));
            M_CASE(uint16_t, CHAR_BIT * sizeof(got));
            M_CASE(uint32_t, CHAR_BIT * sizeof(got));
            M_CASE(U64, CHAR_BIT * sizeof(got));
            M_CASE(BigInt, got.bit_length);
            case Util::Type::index<PrimVar, bool>: {
                UTIL_THROW(Util::Err::Usage, "Not supported for booleans");
            };
            default: {
                UTIL_THROW(Util::Err::Unknown, "unknown type in variant; report this");
            };
        }
    }

    /** Ostream operator for PrimVar */
    inline std::ostream &operator<<(std::ostream &o, const PrimVar &v) {
        static_assert(std::variant_size_v<PrimVar> == 10, "Fix me");
        switch (v.index()) {
            M_CASE(bool, o << std::boolalpha << got);
            M_CASE(std::string, o << std::quoted(got));
            M_CASE(float, o << got);
            M_CASE(double, o << got);
            M_CASE(PyObj::VS::Ptr, o << got);
            M_CASE(uint8_t, o << static_cast<uint16_t>(got));
            M_CASE(uint16_t, o << got);
            M_CASE(uint32_t, o << got);
            M_CASE(U64, o << got);
            M_CASE(BigInt, o << got);
            default:
                UTIL_THROW(Util::Err::Unknown, "unknown type in variant; report this");
        }
    }
#undef M_CASE

} // namespace Op

#endif
