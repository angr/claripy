#include <string>
#include <stdio.h>

// Forward declarations
class ASTBase;


// AST Cache Key class
class ASTCacheKey {
public:
	ASTCacheKey(const ASTBase & a);
	char * repr() const;
private:
	// Representation
	const ASTBase & ref;
};

// ASTCacheKey comparison
bool operator==(const ASTCacheKey & a, const ASTCacheKey & b);
