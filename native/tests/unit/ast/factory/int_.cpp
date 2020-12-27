/** @file */

#include "ast/factory.hpp"
#include "ast/int.hpp"
#include "ops/operations.hpp"

#include <set>


/** Test creating an AST::Int */
int int_() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::Int>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
