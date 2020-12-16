/**
 * @file manager.hpp
 * @brief Define the Simplification::Manager class
 */
#ifndef __SIMPLIFICATIONS_MANAGER_HPP__
#define __SIMPLIFICATIONS_MANAGER_HPP__

#include "../ast/using_declarations.hpp"
#include "../ops/operations_enum.hpp"

#include <map>
#include <memory>


/** A namespace used for the simplifications directory */
namespace Simplifications {

    /** Return if_true, if_false, or None depending on what cond evaluates to */
    AST::Base if_simplifier(const AST::Base original, const AST::Bool &cond,
                            const AST::Base &if_true, const AST::Base &if_false);

} // namespace Simplifications

#endif
