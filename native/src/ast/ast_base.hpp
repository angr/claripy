#ifndef __AST_BASE_HPP__
#define __AST_BASE_HPP__

// Forward declarations
class ASTCacheKey;

// Simplify enum
enum class Simplify {
	UN,
	FULL,
	LITE
};

// Repr enum
enum class Repe {
	LITE,
	MID,
	FULL
};

/*
This is the base class of all claripy ASTs. An AST tracks a tree of operations on arguments.
This class should not be instanciated directly - instead, use one of the constructor functions (BVS, BVV, FPS,
FPV...) to construct a leaf node and then build more complicated expressions using operations.
AST objects have *hash identity*. This means that an AST that has the same hash as another AST will be the *same*
object. This is critical for efficient memory usage. As an example, the following is true::
	a, b = two different ASTs
	c = b + a
	d = b + a
	assert c is d
*/
class Base {
public:

	static factory(

protected:


private:
	Base();

	// Friends
	friend class ASTCacheKey;
	friend bool operator==(const ASTCacheKey & a, const ASTCacheKey & b);
};


#endif
