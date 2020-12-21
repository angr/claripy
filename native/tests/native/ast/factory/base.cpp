/** @file */

#include "src/ast/base.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations_enum.hpp"

#include <set>

/** A place holder test
 *  @todo make this a real test
 */
int base() {
    std::set<AST::BackendID> s;
    (void) AST::factory<AST::Base>(std::move(s), std::move((Ops::Operation) 0));
    return 0;
}
