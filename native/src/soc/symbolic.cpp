/** @file */
#include "symbolic.hpp"


// For brevity
using namespace SOC;

/** The hash functor */
static std::hash<std::string> hasher;


Symbolic::Symbolic(const std::string &n) : Base { hasher(n) }, name { n } {}

bool Symbolic::symbolic() const noexcept {
    return true;
}
