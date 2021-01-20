/**
 * @file
 * @brief Define a map from Op::Operations to a Simplifier
 */
#ifndef __SIMPLIFICATION_PRIVATE_OPMAP_HPP__
#define __SIMPLIFICATION_PRIVATE_OPMAP_HPP__

#include "../../op.hpp"
#include "../constants.hpp"

#include <map>


namespace Simplification::Private {

    /** A map which maps operations to a simplifiers that can handle it */
    extern const std::map<Op::Operation, SimplifierFunc &> op_map;

} // namespace Simplification::Private

#endif
