/** @file */

#include "ast/bits.hpp"

#include "testlib.hpp"

#include <set>

// For brevity
using namespace AST;
using namespace UnitTest::TestLib;


/** Test creating an AST::Bits */
int bits_bits() {
    Bits a = construct_ast<Bits>((Op::Operation) 0, 0);
    Bits b = construct_ast<Bits>((Op::Operation) 1, 0);
    if (a != b) {
        return 0;
    }
    else {
        return 1;
    }
}
