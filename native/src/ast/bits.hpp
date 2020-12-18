/**
 * @file
 * @brief This file defines AST::Bits
 */
#ifndef __AST_Bits_HPP__
#define __AST_Bits_HPP__

#include "raw_types/bits.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** An abbreviation for a shared pointer to the cached Bits class */
    using Bits = std::shared_ptr<RawTypes::Bits>;
} // namespace AST

#endif
