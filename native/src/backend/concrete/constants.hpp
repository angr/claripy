/**
 * @file
 * @brief This file defines concrete backend constants
 */
#ifndef R_BACKEND_CONCRETE_CONSTANTS_HPP_
#define R_BACKEND_CONCRETE_CONSTANTS_HPP_

#include "../generic.hpp"

namespace Backend::Concrete {

    /** The data type to be used as the BackendObject */
    using PrimVar = Op::Literal::Data;

    /** The 'Generic' superclass of z3 */
    using Super = Generic<PrimVar, false>;

} // namespace Backend::Concrete

#endif
