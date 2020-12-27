/** @file */

#include "src/ast/bv.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations.hpp"

#include <set>


/** Test creating an AST::BV */
int bv() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::BV>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
