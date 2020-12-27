/** @file */

#include "ast/bool.hpp"
#include "ast/factory.hpp"
#include "ops/operations.hpp"

#include <set>


/** Test creating an AST::Bool */
int bool_() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::Bool>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
