/** @file */

#include "src/ast/base.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations_enum.hpp"

#include <set>

/** Construct a Base */
AST::Base construct() {
    std::set<AST::BackendID> s;
    return AST::factory<AST::Base>(std::move(s), std::move((Ops::Operation) 0));
}

/** Two bases should be the same */
int base_base() {
    AST::Base a = construct();
    AST::Base b = construct();
    if (a == b) {
        return 0;
    }
    else {
        return 1;
    }
}
