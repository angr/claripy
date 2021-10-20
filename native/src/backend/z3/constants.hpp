/**
 * @file
 * @brief This file defines Z3 backend constants
 */
#ifndef R_BACKEND_Z3_CONSTANTS_HPP_
#define R_BACKEND_Z3_CONSTANTS_HPP_

#include "../generic.hpp"


namespace Backend::Z3 {

    /** A map used for translocating annotations between symbols
     *  It assists in translocations between pre-conversion and post-abstraction exprs
     */
    using SymAnTransData = std::map<uint64_t, Annotation::SPAV>;

    /** The designated NaN for the given type that the Z3 backend uses */
    template <typename T>
    inline static const constexpr T nan { std::numeric_limits<T>::quiet_NaN() };

    /** A variant of primitives the z3 backend uses */
    using PrimVar = Op::Literal::Data;

    /** What rewriter.hi_fp_unspecified is set to */
    const constexpr bool rhfpu { true };

} // namespace Backend::Z3

#endif
