/** @file */
#include "literal.hpp"

#include "../../../utils.hpp"


// Avoid magic numbers
#define SIXTY_FOUR 64
#define ONE_TWENTY_EIGHT 128


// For brevity
using namespace Utils::Error::Unexpected;
namespace MP = boost::multiprecision;
using namespace Expression::Raw;
using namespace Op;
using Val = Literal::ValueT;


/** Construct a Val whose type depends on size
 * @todo
 */
static inline Val create_value(const std::string &rdata, const CUSized::SizeT size) {
    if (size <= SIXTY_FOUR) {
        Utils::affirm<IncorrectUsage>(rdata.size() == SIXTY_FOUR / CHAR_BIT,
                                      "Literal constructor with size ", size,
                                      " given a string with less than 8 bytes in it");
        Constants::CCSC data = rdata.data();
        return Val(Utils::type_pun<int_fast64_t>(data));
    }
    else if (size <= ONE_TWENTY_EIGHT) {
        Constants::CCSC data = rdata.data();
        return Val(MP::int128_t(data));
    }
    else {
        return Val(MP::mpz_int(rdata));
    }
}

Literal::Literal(const std::string &data) : value(create_value(data, this->size)) {}

Literal::~Literal() noexcept = default;

Constants::CCS Literal::op() const {
    return "Literal";
}
