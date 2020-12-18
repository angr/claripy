/**
 * @file
 * @brief This file defines AST::BV
 */
#ifndef __AST_BV_HPP__
#define __AST_BV_HPP__

#include "raw_types/bv.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** An abbreviation for a shared pointer to the cached BV class */
    using BV = std::shared_ptr<RawTypes::BV>;
} // namespace AST

#endif
