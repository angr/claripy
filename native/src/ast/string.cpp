/** @file */
#include "string.hpp"

#include "../ops/operations_enum.hpp"


// For clarity
using namespace AST;
using Op = Ops::Operation;

/* String Cached::String::Concrete(const std::string & value, const Constants::Int length) { */
/* 	if (value.length() > length) { */
/* 		throw Errors::Python::ValueError("Can't make a concrete string value longer than
 * the specified length!"); */
/* 	} */
/* 	return Cached::String::factory(Op::StringV, (value, len(value)), length=length, **kwargs)
 */
/* } */

// Return the name of the type this class represents
std::string Cached::String::fundamental_type_name() const {
    return "AST::String";
}

/** @todo make this actually work */
Hash Cached::String::hash(const Ops::Operation o, const Constants::Int length) {
    return Hash(o);
}
