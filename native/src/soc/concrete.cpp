/** @file */
#include "concrete.hpp"


// For brevity
using namespace SOC;


Concrete::Concrete() : Base(hash()) {}

std::size_t Concrete::hash() {
    return 0;
}

bool Concrete::symbolic() const noexcept {
    return false;
}
