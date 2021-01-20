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
/** @todo implement */
std::string CacheKey::repr() const {
    std::ostringstream ret;
	ret << this->ref.id;
    return ret.str();
}

// CacheKey comparison
bool CacheKey::operator==(const CacheKey &b) const {
    return this->ref.id == b.ref.id;
}
