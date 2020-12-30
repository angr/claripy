/** @file */
#include "if.hpp"

#include "../../op/operations.hpp"
#include "../../utils.hpp"


// For brevity
using namespace Utils;
using namespace Error;
namespace IOp = Interface::Op;


IOp::If::If(const AST::Base &b) : IOp::Op(b, ::Op::Operation::If) {
    Utils::affirm<Unexpected::Interface>(this->size() == 3, WHOAMI_WITH_SOURCE
                                         " -- "
                                         "If interface AST must have exactly 3 children");
}

AST::Base IOp::If::cond() const {
    return this->child(0);
}

AST::Base IOp::If::if_true() const {
    return this->child(1);
}

AST::Base IOp::If::if_false() const {
    return this->child(2);
}
