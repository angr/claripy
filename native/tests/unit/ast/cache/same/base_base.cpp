/** @file */

#include "ast/base.hpp"

#include "ast/factory.hpp"
#include "op/operations.hpp"

#include <set>

/** Construct a Base */
AST::Base construct() {
    std::set<AST::BackendID> s;
    return AST::factory<AST::Base>(std::move(s), std::move((Op::Operation) 0));
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
