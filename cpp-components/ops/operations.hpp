#ifndef __OPERATIONS__
#define __OPERATIONS__

#include "operations_enum.hpp"
#include <set>

// Put everything in the Ops namespace
namespace Ops {
	using OpSet = std::set<Operations>;

	namespace Expression {
		extern const OpSet
			arithmetic,
			comparator,
			bitwise,
			set,
			operations;
	};

	extern const OpSet bin_ops;

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
			ops,
			concrete,
			symbolic;
	}

	extern const OpSet not_invertible;
	extern const OpSet reverse_distributable;

	/* namespace Maps { */
/* opposites */
/* reversed_ops */
/* inverse_operations */
/* infix */

	/* } */

	extern const OpSet commutative;
}

#endif
