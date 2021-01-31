/** @file */
#include "base.hpp"


// For brevity
using namespace SOC;


Base::Base(const std::size_t h) : hash(h) {}

std::size_t std::hash<Base>::operator()(const SOC::Base &b) const noexcept {
    return b.hash;
}
