/** @file */

#include "src/ast/bits.hpp"

#include "src/ast/factory.hpp"
#include "src/ops/operations_enum.hpp"

#include <set>

/** Construct a Bits */
AST::Bits construct(Ops::Operation o) {
    std::set<AST::BackendID> s;
    return AST::factory<AST::Bits>(std::move(s), std::move(o), std::move(0));
}

/** Test creating an AST::Bits */
int bits_bits() {
    AST::Bits a = construct((Ops::Operation) 0);
    AST::Bits b = construct((Ops::Operation) 1);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
