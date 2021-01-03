/** @file */
#include "base.hpp"

#include "../utils.hpp"


// For brevity
using namespace Utils;
namespace Unexpected = Error::Unexpected;


Interface::Base::Base(const AST::Base &b) : ast(b) {}

Interface::Base::~Base() {}

Constants::UInt Interface::Base::size() const {
    static const Constants::UInt size = this->ast->children.size();
    return size;
}

AST::Base Interface::Base::child(const Constants::UInt index) const {
    Utils::affirm<Unexpected::Interface>(index < this->size(),
                                         WHOAMI_WITH_SOURCE
                                         " -- "
                                         "Accessing AST children out of bounds with index: ",
                                         index);
    return this->ast->children[index];
}
