/** @file */

#include "src/ast/factory.hpp"
#include "src/ast/int.hpp"
#include "src/ops/operations.hpp"

#include <set>


/** Test creating an AST::Int */
int int_() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::Int>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
