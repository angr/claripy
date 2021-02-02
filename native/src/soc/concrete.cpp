/** @file */
#include "concrete.hpp"

#include "../utils.hpp"


// For brevity
using namespace SOC;


Concrete::Concrete() : Base { hash() } {}

Hash::Hash Concrete::hash() {
    return UTILS_FILE_LINE_HASH;
}

bool Concrete::symbolic() const noexcept {
    return false;
}
