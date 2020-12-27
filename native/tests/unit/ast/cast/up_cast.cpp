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

/* up_casting should succeed */
int up_cast() {
    Int a = construct<Int>();
    Base b = up_cast<Base>(a);
    if (b != nullptr) {
        return 0;
    }
    // This *should* be impossible
    else {
        return 1;
    }
}
