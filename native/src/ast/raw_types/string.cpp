/** @file */
#include "string.hpp"

#include "../../ops/operations_enum.hpp"
#include "../../utils/inc.hpp"


// Define required AST functions
AST_RAWTYPES_DEFINE_AST_SUBBASE_ID_FUNCTIONS(String)


// For clarity
using namespace AST;
using Op = Ops::Operation;


/** @todo */
RawTypes::String::String(const Hash h, const Ops::Operation o) : RawTypes::Bits(h, o, 0) {}


/* String RawTypes::String::Concrete(const std::string & value, const Constants::Int length) { */
/* 	if (value.length() > length) { */
/* 		throw Errors::Python::ValueError("Can't make a concrete string value longer than
 * the specified length!"); */
/* 	} */
/* 	return RawTypes::String::factory(Op::StringV, (value, len(value)), length=length, **kwargs)
 */
/* } */

/** @todo make this actually work */
Hash RawTypes::String::hash(const Ops::Operation o) {
    return Hash(String::static_class_id) * (1 + Hash(o));
}
