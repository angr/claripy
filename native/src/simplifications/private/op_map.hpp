/**
 * @file
 * @brief Define a map from Ops::Operations to a Simplifier
 */
#ifndef __SIMPLIFICATIONS_PRIVATE_OPMAP_HPP__
#define __SIMPLIFICATIONS_PRIVATE_OPMAP_HPP__

#include "../../ops/operations.hpp"
#include "../simplifiers.hpp"

#include <map>


namespace Simplifications::Private {

    /** A map which maps operations to a simplifiers that can handle it */
    extern const std::map<Ops::Operation, Simplifier &> op_map;

} // namespace Simplifications::Private

#endif
