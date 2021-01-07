/** @file */
#include "bits.hpp"

#include "../../../utils.hpp"

#include <sstream>
#include <utility>


// Define class id functions
EXPRESSION_RAW_TYPE_DEFINE_CLASS_IDS(Bits)


// For brevity
using namespace Expression::Raw::Type;


Bits::~Bits() {}

/** @todo */
Bits::Bits(const Hash h, const Constants::Int l) : Base(h), length(l) {}

/** @todo change this */
Expression::Hash Bits::hash(const Constants::Int l) {
    return Hash(Bits::static_class_id) + l;
}

// A special definition of type_name
std::string Bits::type_name() const {
    auto s = std::set<BackendID>();
    std::stringstream ret;
    ret << this->fundamental_type_name() << this->length;
    return ret.str();
}

#if 0
void Bits::check_replaceability(const ::Expression::Bits &old, const ::Expression::Bits &new_) {
    if (old->length != new_->length) {
        throw Error::Expression::Base("Replacements must have matching sizes");
    }
}
#endif
