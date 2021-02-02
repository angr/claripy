/** @file */
#include "symbolic.hpp"

#include "../utils.hpp"


// For brevity
using namespace SOC;

/** The hash functor */
static const std::hash<std::string> hasher;


Symbolic::Symbolic(const std::string &n) : Base { hash(n) }, name { n } {}

Hash::Hash Symbolic::hash(const std::string &s) {
    return UTILS_FILE_LINE_HASH + hasher(s);
}

bool Symbolic::symbolic() const noexcept {
    return true;
}
