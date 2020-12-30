/** @file */
#include "base.hpp"


// For clarity
using namespace Annotation;


Base::~Base() {}

bool Base::eliminatable() const {
    return true;
}

bool Base::relocatable() const {
    return false;
}

const Base *Base::relocate(const AST::Base &src, const AST::Base &dst) const {
    (void) src;
    (void) dst;
    return this;
}
