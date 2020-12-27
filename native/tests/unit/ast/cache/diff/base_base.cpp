/** @file */

#include "src/ast/base.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations.hpp"

#include <set>

/** Construct a Base */
AST::Base construct(Ops::Operation o) {
    std::set<AST::BackendID> s;
    return AST::factory<AST::Base>(std::move(s), std::move(o));
}

/** Two bases should be different */
int base_base() {
    AST::Base a = construct((Ops::Operation) 0);
    AST::Base b = construct((Ops::Operation) 1);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
