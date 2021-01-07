/** @file */
#include "cache_key.hpp"

#include "raw/type/base.hpp"

#include <sstream>
#include <string>


// For clarity
using namespace Expression;


// Constructor
CacheKey::CacheKey(const Raw::Type::Base &a) : ref(a) {}

// __repr__
std::string CacheKey::repr() const {
    std::stringstream ret;
    ret << "<Key " << this->ref.type_name() << ' ' << this->ref.repr(true) << '>';
    return ret.str();
}

// CacheKey comparison
bool CacheKey::operator==(const CacheKey &b) const {
    return this->ref.id == b.ref.id;
}
