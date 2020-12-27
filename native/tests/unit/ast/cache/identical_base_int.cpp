/** @file */

#include "src/ast/base.hpp"
#include "src/ast/cast.hpp"
#include "src/ast/factory.hpp"
#include "src/ast/int.hpp"
#include "src/ops/operations.hpp"

#include <set>


// For brevity
using namespace AST;


/** Construct a Base */
template <typename T> T construct() {
    std::set<BackendID> s;
    return factory<T>(std::move(s), std::move((Ops::Operation) 0));
}

/** Hashing must take into account type differences */
int identical_base_int() {
    Base a = construct<Base>();
    Int b = construct<Int>();
    Base b2 = up_cast<Base>(b);
    if (a != b2) {
        return 0;
    }
    else {
        return 1;
    }
}
