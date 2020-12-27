/** @file */

#include "ast/vs.hpp"

#include "ast/factory.hpp"
#include "ops/operations.hpp"

#include <set>


/** Test creating an AST::VS */
int vs() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::VS>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
