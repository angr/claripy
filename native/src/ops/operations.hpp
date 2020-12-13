/**
 * @file operations.hpp
 * @brief Organizes our operations into sets
 */
#ifndef __OPERATIONS__
#define __OPERATIONS__

#include <map>
#include <set>

#include "operations_enum.hpp"


/** A namespace used for the ops directory */
namespace Ops {
	/** A map from operations to operations */
	using OpMap = std::map<Operations, Operations>;
	/** A set of operations */
	using OpSet = std::set<Operations>;

	/** These sets classify different Expression operations */
	namespace Expression {
		extern const OpSet
			arithmetic,
			comparator,
			bitwise,
			set,
			operations;
	};

	/** These sets classify different Backend operations */
	namespace Backend {
		extern const OpSet
			comparator,
			bitwise,
			boolean,
			bitmod,
			creation,
			symbol_creation,
			vsa_creation,
			other,
			arithmetic,
			operations,
			operations_vsa_compliant,
			operations_all,
			fp_cmp,
			fp,
			strings;
	}

	/** These sets classify different Length operations */
	namespace Length {
		extern const OpSet
			same,
			none,
			change,
			new_;
	}

	/** These sets classify different Leaf operations */
	namespace Leaf {
		extern const OpSet
			operations,
			concrete,
			symbolic;
	}

	// Miscellaneous classification sets
	extern const OpSet
		bin_ops,
		not_invertible,
		reverse_distributable,
		commutative;

	/** These maps operations to related operations */
	namespace Maps {
		extern const OpMap
			opposites,
			reversed,
			inverse;
	}

	// This maps operations to their infix notations
	extern const std::map<Operations, const char * const> infix;
}

#endif
