/**
 * @file
 * @brief This file defines concrete backend constants
 */
#ifndef R_SRC_BACKEND_CONCRETE_CONSTANTS_HPP_
#define R_SRC_BACKEND_CONCRETE_CONSTANTS_HPP_

#include "../generic.hpp"

namespace Backend::Concrete {

    /** The data type to be used as the BackendObject */
    using PrimVar = Op::Literal::Data;

} // namespace Backend::Concrete

#endif
