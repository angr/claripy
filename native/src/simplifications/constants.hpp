/**
 * @file
 * @brief This file contains constants used within the simplifications directory
 */
#ifndef __SIMPLIFICATIONS_CONSTANTS_HPP__
#define __SIMPLIFICATIONS_CONSTANTS_HPP__

#include "../ast/using_declarations.hpp"


/** A namespace used for the simplifications directory */
namespace Simplifications {

    /** The type each top level simplifier must have */
    using Simplifier = AST::Base(const AST::Base &);

} // namespace Simplifications

#endif
