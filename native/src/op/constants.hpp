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
                                 PyObj::VSPtr   // VS
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

} // namespace Op

#endif
