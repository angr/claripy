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

/** Test creating an Base */
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
