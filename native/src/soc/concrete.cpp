/** @file */
#include "concrete.hpp"


// For brevity
using namespace SOC;


Concrete::Concrete() : Base(0) {}


bool Concrete::symbolic() const noexcept {
    return false;
}
