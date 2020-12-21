/** @file */

#include "src/ast/bool.hpp"
#include "src/ast/factory.hpp"
#include "src/ops/operations_enum.hpp"

#include <set>


/** Test creating an AST::Bool */
int bool_() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::Bool>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
