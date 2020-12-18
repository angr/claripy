/**
 * @file
 * @brief This file defines AST::Bool
 */
#ifndef __AST_Bool_HPP__
#define __AST_Bool_HPP__

#include "raw_types/bool.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** An abbreviation for a shared pointer to the cached Boolclass */
    using Bool = std::shared_ptr<RawTypes::Bool>;
} // namespace AST

#endif
