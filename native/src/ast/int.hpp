/**
 * @file
 * @brief This file defines AST::Int
 */
#ifndef __AST_Int_HPP__
#define __AST_Int_HPP__

#include "raw_types/int.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** An abbreviation for a shared pointer to the cached Int class */
    using Int = std::shared_ptr<RawTypes::Int>;
} // namespace AST

#endif
