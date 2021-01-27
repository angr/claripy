/** @file */
#include "concrete.hpp"


// For brevity
using namespace Expression::Raw;


Concrete::~Concrete() = default;

bool Concrete::symbolic() const {
    return false;
}
