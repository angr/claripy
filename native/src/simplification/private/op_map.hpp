/**
 * @file
 * @brief Define a map from Ops::Operations to a Simplifier
 */
#ifndef __SIMPLIFICATION_PRIVATE_OPMAP_HPP__
#define __SIMPLIFICATION_PRIVATE_OPMAP_HPP__

#include "../../ops/operations.hpp"
#include "../simplifiers.hpp"

#include <map>


namespace Simplification::Private {

    /** A map which maps operations to a simplifiers that can handle it */
    extern const std::map<Ops::Operation, SimplifierFunc &> op_map;

} // namespace Simplifications::Private

#endif
