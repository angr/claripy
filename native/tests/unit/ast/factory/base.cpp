/** @file */

#include "src/ast/base.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations.hpp"

#include <set>


/** Test creating an AST::Base */
int base() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::Base>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
