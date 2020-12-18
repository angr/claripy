/** @file */
#include "simplify.hpp"

#include "private/op_map.hpp"

#include "../ast/base.hpp"


// For simplicity
using namespace Simplifications;


AST::Base simplify(const AST::Base &old) {
    auto lookup = Private::op_map.find(old->op);
    if (lookup != Private::op_map.end()) {
        return lookup->second(old);
    }
    else {
        return old;
    }
}
