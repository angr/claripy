/** @file */

#include "src/ast/base.hpp"
#include "src/ast/cast.hpp"
#include "src/ast/factory.hpp"
#include "src/ast/int.hpp"
#include "src/ops/operations_enum.hpp"

#include <set>


// For brevity
using namespace AST;


/** Construct a Base */
template <typename T> T construct() {
    std::set<BackendID> s;
    return factory<T>(std::move(s), std::move((Ops::Operation) 0));
}

/* Down casting should succeed */
int down_cast_throw() {
    Int a = construct<Int>();
    Base b = up_cast<Base>(a);
    Int c = down_cast_throw_on_fail<Int>(a);
    if (c == a) {
        return 0;
    }
    else {
        return 1;
    }
}
