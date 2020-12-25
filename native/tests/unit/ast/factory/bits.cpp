/** @file */

#include "src/ast/bits.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations_enum.hpp"

#include <set>


/** Test creating an AST::Bits */
int bits() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::Bits>(std::move(s), std::move((Ops::Operation) 0), std::move(0));
    return 0;
}
