/** @file */

#include "ast/base.hpp"
#include "ast/cast.hpp"
#include "ast/factory.hpp"
#include "ast/int.hpp"
#include "ops/operations.hpp"

#include <set>


// For brevity
using namespace AST;


/** Construct a Base */
template <typename T> T construct() {
    std::set<BackendID> s;
    return factory<T>(std::move(s), std::move((Ops::Operation) 0));
}

/* Down casting should succeed */
int down_cast() {
    Int a = construct<Int>();
    Base b = up_cast<Base>(a);
    Int c = down_cast<Int>(a);
    if (c == a) {
        return 0;
    }
    else {
        return 1;
    }
}
