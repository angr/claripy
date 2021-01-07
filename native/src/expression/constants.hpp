/**
 * @file
 * @brief This file defines constants used within the AST namespace
 */
#ifndef __AST_CONSTANTS_HPP__
#define __AST_CONSTANTS_HPP__

#include "../constants.hpp"


namespace AST {

    /** Define a type to store hashes */
    using Hash = uint_fast64_t;

    /** Define a type to store backend IDs */
    using BackendID = Constants::Int;

} // namespace AST

#endif
