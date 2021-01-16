/** @file */
#include "literal.hpp"


// For brevity
namespace MP = boost::multiprecision;
using namespace Expression::Raw;
using namespace Op;
using Val = Literal::ValueT;


/** Construct a Val whose type depends on size
 * @todo
 */
static inline Val create_value(Constants::CCSC data, const CUSized::SizeT size) {
	if (size <= 64) {
		return Val( *((int_fast64_t*) data) );
	}
	else if (size <= 128) {
		return Val( MP::int128_t(data) );
	}
	else {
		return Val( MP::mpz_int(data) );
	}
}

Literal::Literal(Constants::CCSC data) : value(create_value(data, this->size)) {}

Literal::~Literal() {}

Constants::CCS Literal::op() const {
    return "Literal";
}
