/** @file */
#include "concrete.hpp"


// For brevity
using namespace Expression::Raw;


Concrete::~Concrete() noexcept = default;

bool Concrete::symbolic() const {
    return false;
}
