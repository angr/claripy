/**
 * @file
 * @brief This file defines Z3 backend constants
 */
#ifndef R_SRC_BACKEND_Z3_CONSTANTS_HPP_
#define R_SRC_BACKEND_Z3_CONSTANTS_HPP_

#include "../generic.hpp"


namespace Backend::Z3 {

    /** A map used for translocating annotations between symbols
     *  It assists in translocations between pre-conversion and post-abstraction exprs
     */
    using SymAnTransData = std::map<U64, Annotation::SPAV>;

    /** The designated NaN for the given type that the Z3 backend uses */
    template <typename T>
    inline static const constexpr T nan { std::numeric_limits<T>::quiet_NaN() };

    /** What rewriter.hi_fp_unspecified is set to */
    const constexpr bool rhfpu { true };

} // namespace Backend::Z3

#endif
