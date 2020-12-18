/**
 * @file
 * @brief Define a map from Ops::Operations to a Simplifier
 */
#ifndef __SIMPLIFICATIONS_PRIVATE_OPMAP_HPP__
#define __SIMPLIFICATIONS_PRIVATE_OPMAP_HPP__

#include "../../ops/operations_enum.hpp"
#include "../simplifiers.hpp"

#include <map>


/** A namespace used for the simplifications directory */
namespace Simplifications {

    /** A namespace used to designate certain items in simplifications as private
     *  These functions should not be called outside of the simplifications directory
     */
    namespace Private {

        /** A map which maps operations to a simplifiers that can handle it */
        extern const std::map<Ops::Operation, Simplifier &> op_map;

    } // namespace Private

} // namespace Simplifications

#endif
