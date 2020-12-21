/** @file */
#include "bits.hpp"

#include "../../errors/ast.hpp"
#include "../../utils/inc.hpp"

#include <sstream>
#include <utility>


// Define required AST functions
DEFINE_AST_SUBBITS_ID_FUNCTIONS(Bits)


// For brevity
using CBits = AST::RawTypes::Bits;


CBits::~Bits() {}

/** @todo */
CBits::Bits(const Hash h, const Ops::Operation o, const Constants::Int l)
    : Base(h, o), length(l) {}

/** @todo change this */
AST::Hash CBits::hash(const Ops::Operation o, const Constants::Int l) {
    return Hash(CBits::static_class_id) * (1 + Hash(o)) + l;
}

// A special definition of type_name
std::string CBits::type_name() const {
    auto s = std::set<BackendID>();
    std::stringstream ret;
    ret << this->fundamental_type_name() << this->length;
    return ret.str();
}

void CBits::check_replaceability(const AST::Bits &old, const AST::Bits &new_) {
    if (old->length != new_->length) {
        throw Errors::AST::Base("Replacements must have matching sizes");
    }
}
