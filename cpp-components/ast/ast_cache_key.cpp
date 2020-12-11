#include <string>
#include <stdio.h>

#include "ast_cache_key.hpp"
#include "ast_base.hpp"


// Constructor
ASTCacheKey::ASTCacheKey(const ASTBase & a) : ref(a) {}

// __repr__
char * ASTCacheKey::repr() const {
	char * ret;
	asprintf(&ret, "<Key %s %s>", ref.type_name(), ref.rep(inner=True));
	return ret;
}

// ASTCacheKey comparison
bool operator==(const ASTCacheKey & a, const ASTCacheKey & b) {
	return a.ref.hash == b.ref.hash;
}
