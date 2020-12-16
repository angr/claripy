/** @file */
#include "bits.hpp"

#include "../errors/errors.hpp"

#include <sstream>
#include <utility>


// For brevity
using CBits = AST::Cached::Bits;


CBits::Bits(const Ops::Operation o, const Hash h, const Constants::Int l)
    : Base(o, h), length(l) {}

Constants::Int CBits::size() const {
    return this->length;
}

std::string CBits::type_name() const {
    std::stringstream ret;
    ret << "Bits" << this->length;
    return ret.str();
}

void CBits::check_replaceability(const AST::Bits &old, const AST::Bits &new_) {
    if (old->size() != new_->size()) {
        throw Errors::AST("Replacements must have matching sizes");
    }
}
