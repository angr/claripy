/** @file */
#include "manager.hpp"

#include "../ast/base.hpp"
#include "../ast/bool.hpp"


// For clarity
using namespace Simplifications;


/** @todo: is the none really needed? I assume so because of things like the if_simplifier */
AST::Base if_simplifier(const AST::Base &original, const AST::Bool &cond, const AST::Base &if_true,
                        const AST::Base &if_false) {
    if (cond->is_true()) {
        return if_true;
    }
    else if (cond->is_false()) {
        return if_false;
    }
    else {
        return original;
    }
}
