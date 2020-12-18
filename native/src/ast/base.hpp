/**
 * @file
 * @brief This file defines AST::Base
 */
#ifndef __AST_BASE_HPP__
#define __AST_BASE_HPP__

#include "raw_types/base.hpp"


/** A namespace used for the ast directory */
namespace AST {

    /** An abbreviation for a shared pointer to the cached Base class */
    using Base = std::shared_ptr<RawTypes::Base>;
} // namespace AST

#endif
