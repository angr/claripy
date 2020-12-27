/** @file */

#include "ast/bits.hpp"

#include "ast/factory.hpp"
#include "ops/operations.hpp"

#include <set>


/** Test creating an AST::Bits */
int bits() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::Bits>(std::move(s), std::move((Ops::Operation) 0), std::move(0));
    return 0;
}
