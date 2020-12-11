#ifndef __OPERATIONS__
#define __OPERATIONS__

#include "operations_enum.hpp"
#include <set>

// Put everything in the Ops namespace
namespace Ops {
	using OpSet = std::set<Operations>;

	// Classify Expression ops
	namespace Expression {
		extern const OpSet
			arithmetic,
			comparator,
			bitwise,
			set,
			operations;
	};

	// Classify Binary ops
	extern const OpSet bin_ops;

	// Classify Backend ops
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
}

#endif
