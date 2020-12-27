/** @file */

#include "src/ast/string.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations.hpp"

#include <set>


/** Test creating an AST::String */
int string() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::String>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
