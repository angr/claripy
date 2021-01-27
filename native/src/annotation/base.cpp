/** @file */
#include "base.hpp"

#include "../expression.hpp"
#include "../utils.hpp"


// For clarity
using namespace Annotation;


Base::~Base() noexcept = default;

Constants::UInt Base::hash() const {
    return Utils::type_id<Base>();
}

bool Base::eliminatable() const {
    return true;
}

bool Base::relocatable() const {
    return false;
}

const Base *Base::relocate(const Expression::Base &src, const Expression::Base &dst) const {
    (void) src;
    (void) dst;
    return this;
}
