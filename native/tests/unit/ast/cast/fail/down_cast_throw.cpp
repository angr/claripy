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

/** Down casting should fail with an exception */
int down_cast_throw() {
    Base a = construct<Base>();
    try {
        Int b = down_cast_throw_on_fail<Int>(a);
    }
    catch (Utils::Error::Unexpected::BadCast &e) {
        return 0;
    }
    return 1;
}
