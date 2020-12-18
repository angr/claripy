/**
 * @file
 * @brief This file defines AST::VS
 */
#ifndef __AST_VS_HPP__
#define __AST_VS_HPP__

#include "raw_types/vs.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** An abbreviation for a shared pointer to the cached vs class */
    using VS = std::shared_ptr<RawTypes::VS>;
} // namespace AST

#endif
