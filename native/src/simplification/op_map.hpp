/**
 * @file
 * @brief Define a map from ops to simplifiers
 */
#ifndef R_SIMPLIFICATION_OPMAP_HPP_
#define R_SIMPLIFICATION_OPMAP_HPP_

#include "simplifiers.hpp"

#include "../op.hpp"

#include <map>


/** Local: A map entry from an op static cuid to a simplifier */
#define MAP_ENTRY(OP, SIMP) { Op::OP::static_cuid, &Simplifier::SIMP },

namespace Simplification {

    /** Map op static cuids to op simplifiers */
    inline const std::map<CUID::CUID, SimplifierFunc *const> op_map { // TODO: pointer
                                                                      MAP_ENTRY(Eq, eq)
    };

} // namespace Simplification

// Cleanup
#undef MAP_ENTRY

#endif
