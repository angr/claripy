/** @file */

#include "ast/fp.hpp"

#include "ast/factory.hpp"
#include "ops/operations.hpp"

#include <set>


/** Test creating an AST::FP */
int fp() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::FP>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
