/**
 * @file base.hpp
 * @brief This file defines the AST::Base class
 */
#ifndef __AST_BASE_HPP__
#define __AST_BASE_HPP__

/** A namespace used for the ast directory */
namespace AST {

	// Forward declarations
	class CacheKey;

	/** A type-safe simplify-level enumeration */
	enum class Simplify {
		UN,
		FULL,
		LITE
	};

	/** A type-safe repr-level enumeration */
	enum class Repr {
		LITE,
		MID,
		FULL
	};

	/** This is the base class of all claripy ASTs.
	 * An AST tracks a tree of operations on arguments.
	 * This class should not be instanciated directly - instead, use one of the constructor functions (BVS, BVV, FPS,
	 * FPV...) to construct a leaf node and then build more complicated expressions using operations.
	 * AST objects have *hash identity*. This means that an AST that has the same hash as another AST will be the *same*
	 * object. This is critical for efficient memory usage. As an example, the following is true::
	 *  a, b = two different ASTs
	 *  c = b + a
	 *  d = b + a
	 *  assert c is d
	 */
	class Base {
		public:

			static factory();

		protected:
			/** A protected constructor to disallow public creation */
			Base();


			// Friends
			/** Allow CacheKey friend-access */
			friend class CacheKey;
			/** Allow CacheKey's equality operator friend-access */
			friend bool operator==(const CacheKey & a, const CacheKey & b);
	};

}
#endif
