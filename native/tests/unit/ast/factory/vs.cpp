/** @file */

#include "src/ast/vs.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations.hpp"

#include <set>


/** Test creating an AST::VS */
int vs() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::VS>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
