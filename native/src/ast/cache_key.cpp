#include "cache_key.hpp"

#include "base.hpp"

#include <stdio.h>
#include <string>


// For clarity
using namespace AST;


// Constructor
CacheKey::CacheKey(const Base &a) : ref(a) {}

// __repr__
char *CacheKey::repr() const {
    char *ret;
    asprintf(&ret, "<Key %s %s>", this->ref.type_name(), this->ref.rep(inner = True));
    return ret;
}

// CacheKey comparison
bool operator==(const CacheKey &a, const CacheKey &b) { return a.ref.hash == b.ref.hash; }
