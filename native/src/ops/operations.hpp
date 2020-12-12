#ifndef __OPERATIONS__
#define __OPERATIONS__

#include "operations_enum.hpp"
#include <map>
#include <set>

// Put everything in the Ops namespace
namespace Ops {
	using OpMap = std::map<Operations, Operations>;
	using OpSet = std::set<Operations>;

	namespace Expression {
		extern const OpSet
			arithmetic,
			comparator,
			bitwise,
			set,
			operations;
	};

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

	namespace Length {
		extern const OpSet
			same,
			none,
			change,
			new_;
	}

	namespace Leaf {
		extern const OpSet
			operations,
			concrete,
			symbolic;
	}

	extern const OpSet
		bin_ops,
		not_invertible,
		reverse_distributable,
		commutative;

	namespace Maps {
		extern const OpMap
			opposites,
			reversed,
			inverse;
	}

	extern const std::map<Operations, const char * const> infix;
}

#endif
