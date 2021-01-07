/** @file */
#include "string.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBASE_ID_FUNCTIONS(String)


// For clarity
using namespace Expression;


Raw::Type::String::~String() {}

/** @todo */
Raw::Type::String::String(const Hash h) : Raw::Type::Bits(h, 0) {}


/* String Raw::Type::String::Concrete(const std::string & value, const Constants::Int length) { */
/* 	if (value.length() > length) { */
/* 		throw Error::Python::ValueError("Can't make a concrete string value longer than
 * the specified length!"); */
/* 	} */
/* 	return Raw::Type::String::factory(Op::StringV, (value, len(value)), length=length,
 * **kwargs)
 */
/* } */

/** @todo make this actually work */
Hash Raw::Type::String::hash() {
    return Hash(String::static_class_id);
}
