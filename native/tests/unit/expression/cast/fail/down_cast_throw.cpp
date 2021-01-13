/**
 * @file
 * \ingroup unittest
 */
#include "expression.hpp"
#include "testlib.hpp"

#include <set>


// For brevity
using namespace Expression;
using namespace UnitTest::TestLib;


/** Down casting should fail with an exception */
int down_cast_throw() {
    ConcreteIntLiteral a = literal_int();
    Base b = up_cast<Base>(a);
    try {
        Bool c = down_cast_throw_on_fail<Bool>(b);
    }
    catch (Utils::Error::Unexpected::BadCast &e) {
        return 0;
    }
    return 1;
}
