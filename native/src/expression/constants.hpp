/**
 * @file
 * @brief This file defines constants used within the Expression namespace
 */
#ifndef __EXPRESSION_CONSTANTS_HPP__
#define __EXPRESSION_CONSTANTS_HPP__

#include "../constants.hpp"


namespace Expression {

    /** Define a type to store hashes */
    using Hash = uint_fast64_t;

    /** Define a type to store backend IDs */
    using BackendID = Constants::Int;

} // namespace Expression

#endif
