/**
 * @file
 * @brief Constants OPs can use
 */
#ifndef R_OP_CONSTANTS_HPP_
#define R_OP_CONSTANTS_HPP_

#include "../big_int.hpp"
#include "../py_obj.hpp"

#include <cstddef>
#include <variant>


namespace Op {

    /** The primitive types a claricpp BV will support */
    using BVTL = Util::TypeList<uint8_t, uint16_t, uint32_t, uint64_t, BigInt>;

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

} // namespace Op

#endif
