/**
 * @file
 * @brief This file defines how the z3 backend converts Claricpp Expressions into Z3 ASTs
 */
#ifndef __BACKEND_Z3_CONVERT_HPP__
#define __BACKEND_Z3_CONVERT_HPP__


#include "ref.hpp"

#include "../../op.hpp"


/********************************************************************/
/*                    Claricpp -> Z3 Conversion                     */
/********************************************************************/


/** This nested class converts claricpp expression to Z3 expressions */
class Converter final {
  private:
    // Delete implict constructors and operators
    SET_IMPLICITS(Converter, delete);

    /** A context reference */
    z3::context &context;

  public:
    /** Constructor: takes in a reference to a Z3 context */
    inline Converter(z3::context &ref) : context { ref } {}

    /** Default destructor */
    inline ~Converter() = default;

    /** The claricpp expression pointer type */
    using ExprPtr = const ExprRawPtr;

    // Conversion functions

    BackendObj /* TODO: or pointer? */ neg(ExprPtr expr) {}
};

#endif
