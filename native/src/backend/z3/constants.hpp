/**
 * @file
 * @brief This file Z3 backend constants
 */
#ifndef R_BACKEND_Z3_CONSTANTS_HPP_
#define R_BACKEND_Z3_CONSTANTS_HPP_

#include "../generic.hpp"

#include <map>
#include <string>
#include <z3++.h>


namespace Backend::Z3 {

    /** The 'Generic' superclass of z3
     */
    using Z3Super = Generic<z3::expr, false>;

    /** A map used for translocating annotations between symbols
     *  It assists in translocations between pre-conversion and post-abstraction expressions
     */
    using SymAnTransData = std::map<std::string, Expression::Base::SPAV>;

} // namespace Backend::Z3

#endif
