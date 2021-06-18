/**
 * @file
 * @brief This file Z3 backend constants
 */
#ifndef R_BACKEND_Z3_CONSTANTS_HPP_
#define R_BACKEND_Z3_CONSTANTS_HPP_

#include "../../expression.hpp"

#include <map>
#include <string>


namespace Backend::Z3 {

    /** The z3 unsigned type */
    using z3u = unsigned;

    /** A map used for translocating annotations between symbols
     *  It assists in translocations between pre-conversion and post-abstraction expressions
     */
    using SymAnTransData = std::map<std::string, Expression::Base::SPAV>;

} // namespace Backend::Z3

#endif
