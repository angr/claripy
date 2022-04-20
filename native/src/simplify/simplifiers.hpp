/**
 * @file
 * @brief Define simplifiers in Simplifications::Simplifier
 */
#ifndef R_SRC_SIMPLIFY_SIMPLIFIERS_HPP_
#define R_SRC_SIMPLIFY_SIMPLIFIERS_HPP_

#include "constants.hpp"


namespace Simplify {

    /** Generates a Vec of built in simplifiers to be used on all Exprs */
    Vec builtin_vec();

    /** Generates a Map of built in simplifiers and which Ops to use them on */
    Map builtin_map();

} // namespace Simplify

#endif
