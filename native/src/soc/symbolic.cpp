/** @file */
#include "symbolic.hpp"


// For brevity
using namespace SOC;

/** The hash functor */
static std::hash<std::string> hasher;


Symbolic::Symbolic(std::string &&n) : Base { hash(n) }, name { n } {}

Symbolic::hash(const std::string &s) {
    return hasher(s);
}

bool Symbolic::symbolic() const noexcept {
    return true;
}
