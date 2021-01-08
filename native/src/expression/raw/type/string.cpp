/** @file */
#include "string.hpp"

#include "../../../utils.hpp"


// Define required Expression functions
EXPRESSION_RAW_TYPE_DEFINE_EXPRESSION_SUBBASE_ID_FUNCTIONS(String)


// For clarity
using namespace Expression::Raw;
using namespace Type;


String::~String() {}

/** @todo */
String::String(const Hash h) : Bits(h, 0) {}


/* String Raw::Type::String::Concrete(const std::string & value, const Constants::Int length) { */
/* 	if (value.length() > length) { */
/* 		throw Error::Python::ValueError("Can't make a concrete string value longer than
 * the specified length!"); */
/* 	} */
/* 	return Raw::Type::String::factory(Op::StringV, (value, len(value)), length=length,
 * **kwargs)
 */
/* } */

/** Get the type of the expression */
Constants::CCSC String::type() const {
    return "String";
}
