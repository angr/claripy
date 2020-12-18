/**
 * @file
 * @brief This file defines AST::String
 */
#ifndef __AST_STRING_HPP__
#define __AST_STRING_HPP__

#include "raw_types/string.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** An abbreviation for a shared pointer to the cached String class */
    using String = std::shared_ptr<RawTypes::String>;
} // namespace AST

#endif
