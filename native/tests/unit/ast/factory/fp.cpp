/** @file */

#include "src/ast/fp.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations.hpp"

#include <set>


/** Test creating an AST::FP */
int fp() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::FP>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
