/**
 * @file
 * @brief This file defines AST::FP
 */
#ifndef __AST_FP_HPP__
#define __AST_FP_HPP__

#include "raw_types/fp.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** An abbreviation for a shared pointer to the cached FP class */
    using FP = std::shared_ptr<RawTypes::FP>;
} // namespace AST

#endif
