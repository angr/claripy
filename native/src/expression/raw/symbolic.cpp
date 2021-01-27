/** @file */
#include "symbolic.hpp"

// For brevity
using namespace Expression::Raw;


Symbolic::~Symbolic() noexcept = default;

bool Symbolic::symbolic() const {
    return true;
}
